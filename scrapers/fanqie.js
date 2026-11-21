/**
 * 番茄小说完结作品追踪爬虫（基于原 fanqie.js 改造）
 *
 * 核心改动：
 * 1. 使用 Playwright 打开番茄书库页面，让网页自身生成动态请求签名（不硬编码 a_bogus）。
 * 2. 监听 book_list/v0 响应并通过页面滚动触发分页，不再限制 50 本。
 * 3. 同时尝试采集完结（stat0）和连载（stat1）书库，用每日状态快照识别状态变化。
 * 4. 记录 A：上次在连载列表、本次进入完结列表；B：本次首次发现的完结作品。
 * 5. 保留原有排名、分类、详情、标签、latest/history JSON 结构，并增加追踪字段。
 *
 * 说明：
 * - 番茄网页路由和接口可能调整；stat0 对应完结页已由用户提供的页面确认。
 * - stat1 作为连载页对应路由尝试使用；若站点改版导致无法采集，脚本会明确告警，
 *   不会把不完整的状态快照覆盖成“完整快照”。
 * - 首次运行只建立基准，不能回溯首次运行之前的真实完结日期。
 */

const https = require('https');
const http = require('http');
const fs = require('fs');
const path = require('path');
const { chromium } = require('playwright');
const { computeRankChange } = require('./rank-change');
const { withRetry } = require('./retry');

// ========== 配置 ==========
const DATA_DIR = path.join(__dirname, '..', 'data', 'fanqie');
const HISTORY_DIR = path.join(DATA_DIR, 'history');
const HEADERS = {
  'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36',
  'Accept-Language': 'zh-CN,zh;q=0.9,en;q=0.8',
};
const PAGE_SIZE = 18;
const REQUEST_DELAY = 500;
const DETAIL_DELAY = 250;
const MAX_SCROLL_ROUNDS = 180;
const STAGNANT_ROUNDS_TO_STOP = 7;
const COMPLETED_URL = 'https://fanqienovel.com/library/stat0/page_1?sort=newest';
const ONGOING_URL = 'https://fanqienovel.com/library/stat1/page_1?sort=newest';
const STATE_PATH = path.join(DATA_DIR, 'status_snapshot.json');
const COMPLETION_HISTORY_PATH = path.join(DATA_DIR, 'completion_history.json');

// ========== 工具函数 ==========
function sleep(ms) { return new Promise(resolve => setTimeout(resolve, ms)); }

function ensureDir(dir) {
  if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
}

function getNowBJT() {
  const now = new Date();
  return new Date(now.getTime() + (now.getTimezoneOffset() + 480) * 60000);
}

function fmtDate(d) {
  return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`;
}

function fmtDateTime(d) {
  return `${fmtDate(d)} ${String(d.getHours()).padStart(2, '0')}:${String(d.getMinutes()).padStart(2, '0')}:${String(d.getSeconds()).padStart(2, '0')}`;
}

function readJson(file, fallback) {
  try {
    if (fs.existsSync(file)) return JSON.parse(fs.readFileSync(file, 'utf8'));
  } catch (e) {
    console.log(`[WARN] 读取 JSON 失败 ${file}: ${e.message}`);
  }
  return fallback;
}

function writeJson(file, data) {
  fs.writeFileSync(file, JSON.stringify(data, null, 2), 'utf8');
}

function uniqueStrings(values) {
  return [...new Set((values || []).map(v => String(v || '').trim()).filter(Boolean))];
}

function decodeHtml(s = '') {
  return String(s)
    .replace(/&amp;/g, '&')
    .replace(/&quot;/g, '"')
    .replace(/&#39;|&apos;/g, "'")
    .replace(/&lt;/g, '<')
    .replace(/&gt;/g, '>')
    .replace(/&nbsp;/g, ' ')
    .trim();
}

function httpGet(url, extraHeaders = {}) {
  return new Promise((resolve, reject) => {
    const lib = url.startsWith('https') ? https : http;

    const req = lib.get(url, {
      headers: { ...HEADERS, ...extraHeaders },
      timeout: 60000,
    }, res => {
      if (res.statusCode >= 300 && res.statusCode < 400 && res.headers.location) {
        req.destroy();
        return httpGet(new URL(res.headers.location, url).href, extraHeaders)
          .then(resolve)
          .catch(reject);
      }

      let data = '';
      res.setEncoding('utf8');
      res.on('data', chunk => data += chunk);
      res.on('end', () => resolve({ status: res.statusCode, data }));
    });

    req.on('error', reject);
    req.on('timeout', () => req.destroy(new Error('timeout')));
  });
}

// ========== 分类映射 ==========
async function buildCategoryGenderMap() {
  console.log('  获取分类列表...');

  const map = {};

  for (const gender of [1, 0]) {
    try {
      const url = `https://fanqienovel.com/api/author/book/category_list/v0/?gender=${gender}`;

      const res = await httpGet(url, { Accept: 'application/json' });
      const json = JSON.parse(res.data);

      if (json.code === 0 && Array.isArray(json.data)) {
        for (const cat of json.data) {
          map[cat.name] = {
            gender: gender === 1 ? '男频' : '女频',
            id: cat.category_id,
          };
        }
      }
    } catch (e) {
      console.log(`  [WARN] 分类获取失败(g=${gender}): ${e.message}`);
    }

    await sleep(250);
  }

  return map;
}

// ========== 书库全量采集：由网页触发带签名的请求 ==========
async function crawlLibraryByPage(browser, pageUrl, label) {
  console.log(`\n  打开${label}书库：${pageUrl}`);

  const context = await browser.newContext({
    userAgent: HEADERS['User-Agent'],
    locale: 'zh-CN',
    viewport: { width: 1440, height: 1000 },
  });

  const page = await context.newPage();

  const booksById = new Map();

  let responseCount = 0;
  let sawHasMoreFalse = false;
  let lastPageIndex = -1;

  const responseErrors = [];

  page.on('response', async response => {
    const url = response.url();

    if (!url.includes('/api/author/library/book_list/v0/')) return;

    try {
      const json = await response.json();

      if (
        json &&
        json.code === 0 &&
        json.data &&
        Array.isArray(json.data.book_list)
      ) {
        responseCount++;

        const params = new URL(url).searchParams;
        const pageIndex = Number(params.get('page_index') || -1);

        if (pageIndex >= 0) {
          lastPageIndex = Math.max(lastPageIndex, pageIndex);
        }

        for (const book of json.data.book_list) {
          if (book && book.book_id != null) {
            const id = String(book.book_id);

            if (!booksById.has(id)) {
              booksById.set(id, book);
            } else {
              booksById.set(id, {
                ...booksById.get(id),
                ...book,
              });
            }
          }
        }

        if (json.data.has_more === false) {
          sawHasMoreFalse = true;
        }

        console.log(
          `    [${label}] 收到第${pageIndex >= 0 ? pageIndex + 1 : '?'}页：${json.data.book_list.length}本，累计${booksById.size}本，has_more=${json.data.has_more}`
        );

      } else if (json && json.code !== 0) {
        responseErrors.push(
          `接口 code=${json.code}, message=${json.message || ''}`
        );
      }

    } catch (e) {
      // 某些响应不是 JSON，忽略，不影响其他请求
    }
  });

  let navigationOk = false;

  try {
    await page.goto(pageUrl, {
      waitUntil: 'domcontentloaded',
      timeout: 60000,
    });

    navigationOk = true;

    await page.waitForTimeout(3500);

    let stagnantRounds = 0;
    let previousCount = 0;

    for (let round = 0; round < MAX_SCROLL_ROUNDS; round++) {

      await page.evaluate(() => {
        window.scrollTo(0, document.body.scrollHeight);
      });

      await page.waitForTimeout(1000);

      // 触发懒加载；逐步滚动比一次滚到底更容易触发列表请求
      await page.evaluate(() => {
        window.scrollBy(
          0,
          -Math.max(300, window.innerHeight * 0.65)
        );
      });

      await page.waitForTimeout(450);

      await page.evaluate(() => {
        window.scrollTo(0, document.body.scrollHeight);
      });

      await page.waitForTimeout(900);

      if (booksById.size > previousCount) {
        previousCount = booksById.size;
        stagnantRounds = 0;
      } else {
        stagnantRounds++;
      }

      if (sawHasMoreFalse && stagnantRounds >= 2) break;

      if (stagnantRounds >= STAGNANT_ROUNDS_TO_STOP) break;

      if (round % 10 === 9) {
        console.log(
          `    [${label}] 滚动进度 ${round + 1}/${MAX_SCROLL_ROUNDS}，累计${booksById.size}本`
        );
      }
    }

  } catch (e) {
    console.log(`  [WARN] ${label}页面加载/滚动失败：${e.message}`);

  } finally {
    await context.close().catch(() => {});
  }

  const books = [...booksById.values()];

  const complete =
    navigationOk &&
    books.length > 0 &&
    sawHasMoreFalse;

  console.log(
    `  ${label}采集结束：${books.length}本，响应${responseCount}次，最大页码${lastPageIndex + 1 || '未知'}，has_more=false=${sawHasMoreFalse}`
  );

  if (responseErrors.length) {
    console.log(
      `  [WARN] ${label}接口提示：${uniqueStrings(responseErrors).join('; ')}`
    );
  }

  return {
    books,
    complete,
    navigationOk,
    responseCount,
    sawHasMoreFalse,
    lastPageIndex,
    errors: responseErrors,
  };
}

// ========== 详情页解析 ==========
function parseDetailPage(html) {
  const info = {};

  const titleMatch = html.match(/<title[^>]*>([\s\S]*?)<\/title>/i);

  if (titleMatch) {
    const title = decodeHtml(
      titleMatch[1].replace(/<[^>]+>/g, '')
    );

    const nameMatch = title.match(
      /^(.+?)(?:完整版|全文|_番茄小说|_番茄)/
    );

    if (nameMatch) {
      info.book_name = nameMatch[1].trim();
    }
  }

  const descMatch =
    html.match(/<meta[^>]+name=["']description["'][^>]+content=["']([^"']*)["']/i)
    || html.match(/<meta[^>]+content=["']([^"']*)["'][^>]+name=["']description["']/i);

  if (descMatch) {
    info.description = decodeHtml(descMatch[1])
      .replace(/^番茄小说提供.*?番茄小说网[。.]?\s*/, '')
      .trim();
  }

  const keywordsMatch =
    html.match(/<meta[^>]+name=["']keywords["'][^>]+content=["']([^"']*)["']/i)
    || html.match(/<meta[^>]+content=["']([^"']*)["'][^>]+name=["']keywords["']/i);

  if (keywordsMatch) {
    const authorMatch = keywordsMatch[1].match(/,([^,]+?)小说/);

    if (authorMatch && !/免费|阅读|章节|下载/.test(authorMatch[1])) {
      info.author = decodeHtml(authorMatch[1]);
    }
  }

  const tags = [];

  for (const match of html.matchAll(
    /<(?:a|span)[^>]*class=["'][^"']*(?:tag|label)[^"']*["'][^>]*>([\s\S]*?)<\/(?:a|span)>/gi
  )) {
    const tag = decodeHtml(
      match[1].replace(/<[^>]+>/g, '')
    );

    if (
      tag &&
      tag.length <= 12 &&
      !/连载中|已完结|完结|连载|免费|阅读|下载/.test(tag)
    ) {
      tags.push(tag);
    }
  }

  const ldMatch = html.match(
    /<script[^>]*type=["']application\/ld\+json["'][^>]*>([\s\S]*?)<\/script>/i
  );

  if (ldMatch) {
    try {
      const ld = JSON.parse(ldMatch[1]);

      if (!info.author && ld.author?.name) {
        info.author = ld.author.name;
      }

      if (ld.dateModified) {
        info.dateModified = ld.dateModified;
      }

      if (typeof ld.image === 'string') {
        info.hdImage = ld.image;
      } else if (
        Array.isArray(ld.image) &&
        typeof ld.image[0] === 'string'
      ) {
        info.hdImage = ld.image[0];
      }

      if (ld.genre) {
        tags.push(...(
          Array.isArray(ld.genre) ? ld.genre : [ld.genre]
        ));
      }

    } catch (_) {}
  }

  info.official_tags = uniqueStrings(tags);

  return info;
}

// ========== 标签推断 ==========
const TAG_RULES = {

  genre_tags: [
    ['悬疑灵异', ['灵异', '鬼怪', '诡异', '恐怖', '惊悚', '捉鬼', '风水', '驱邪', '道士']],
    ['科幻末世', ['末世', '末日', '丧尸', '废土', '科幻', '星际', '赛博', '机器人', '人工智能']],
    ['游戏体育', ['游戏', '副本', '电竞', '网游', '体育', '足球', '篮球']],
    ['东方仙侠', ['修仙', '修真', '仙侠', '飞升', '修炼', '仙门', '修道']],
    ['传统玄幻', ['玄幻', '异世', '斗气', '魔法', '龙族', '魔王', '勇者']],
    ['历史古代', ['大唐', '大秦', '三国', '朝廷', '太子', '皇帝', '科举', '王爷', '郡主', '公主']],
    ['都市', ['都市', '职场', '公司', '总裁', '大学', '校园']],
    ['古代言情', ['嫡女', '侯府', '王妃', '古言', '庶女', '宅斗', '宫斗']],
    ['现代言情', ['甜宠', '恋爱', '男友', '闪婚', '破镜重圆', '现言']],
    ['娱乐圈', ['娱乐圈', '明星', '偶像', '演员', '导演', '综艺']],
  ],

  plot_tags: [
    ['系统', ['系统', '金手指', '签到系统']],
    ['穿越', ['穿越', '穿书']],
    ['重生', ['重生', '回到过去', '再活一世']],
    ['空间', ['空间', '随身仓库']],
    ['复仇', ['复仇', '报仇', '血仇']],
    ['升级流', ['升级', '突破境界', '等级提升']],
    ['末日求生', ['末日求生', '生存物资', '避难所']],
    ['种田', ['种田', '开荒', '农场']],
    ['美食', ['美食', '厨艺', '做菜']],
    ['直播', ['直播', '主播', '打赏']],
    ['无限流', ['无限流', '无限世界', '副本任务']],
    ['模拟器', ['模拟器', '人生模拟', '模拟人生']],
  ],

  character_tags: [
    ['女强', ['女强', '女主强势', '大女主']],
    ['多女主', ['多女主', '后宫', '群芳']],
    ['单女主', ['单女主', '一生一世一双人']],
    ['群像', ['群像', '众生相', '多主角']],
    ['天才', ['天才', '绝世天骄']],
    ['反派主角', ['反派', '反派主角', '大反派']],
  ],

  setting_tags: [
    ['现代', ['现代', '都市', '当代']],
    ['古代', ['古代', '大唐', '大明', '大秦', '王朝']],
    ['架空', ['架空', '异世界']],
    ['未来', ['未来', '星际', '赛博']],
    ['末世', ['末世', '末日', '废土']],
    ['校园', ['校园', '大学', '高中', '学生']],
    ['娱乐圈', ['娱乐圈', '明星', '演员']],
  ],

  style_tags: [
    ['搞笑', ['搞笑', '爆笑', '沙雕', '欢乐']],
    ['热血', ['热血', '燃向', '战斗']],
    ['爽文', ['爽文', '爽感', '打脸']],
    ['慢热', ['慢热', '细水长流']],
    ['轻松', ['轻松', '日常', '温馨']],
    ['黑暗', ['黑暗', '黑化', '残酷']],
    ['烧脑', ['烧脑', '反转', '解谜']],
  ],
};

function inferTags(title, desc) {
  const text = `${title || ''} ${desc || ''}`.toLowerCase();

  const result = {};

  for (const [group, rules] of Object.entries(TAG_RULES)) {
    result[group] = [];

    for (const [tag, keywords] of rules) {
      if (
        keywords.some(keyword => text.includes(keyword.toLowerCase()))
      ) {
        result[group].push(tag);
      }
    }
  }

  return result;
}

function inferCategoryFromText(title, desc) {
  const tags = inferTags(title, desc);
  return tags.genre_tags[0] || null;
}

// ========== 状态追踪 ==========
function classifyCompletion(
  currentCompleted,
  currentOngoing,
  previousState,
  today
) {
  const previousCompleted = new Set(
    previousState?.completed_ids || []
  );

  const previousOngoing = new Set(
    previousState?.ongoing_ids || []
  );

  const currentCompletedIds = new Set(
    currentCompleted.map(b => String(b.book_id))
  );

  const currentOngoingIds = new Set(
    currentOngoing.map(b => String(b.book_id))
  );

  const records = [];

  for (const book of currentCompleted) {
    const id = String(book.book_id);

    let completionType = '历史已收录';
    let detectedDate = previousState?.last_successful_date || null;

    if (
      previousOngoing.has(id) &&
      !previousCompleted.has(id)
    ) {
      completionType = '当天新完结';
      detectedDate = today;

    } else if (!previousCompleted.has(id)) {
      completionType = previousState ? '首次发现' : '基准快照';
      detectedDate = previousState ? today : null;
    }

    records.push({
      book_id: id,
      completion_type: completionType,
      first_seen_date: previousState?.first_seen?.[id] || today,
      completed_detected_date:
        completionType === '当天新完结'
          ? today
          : (
            previousState?.completed_detected?.[id]
            || detectedDate
          ),
    });
  }

  const firstSeen = {
    ...(previousState?.first_seen || {}),
  };

  const completedDetected = {
    ...(previousState?.completed_detected || {}),
  };

  for (const book of currentCompleted) {
    const id = String(book.book_id);

    if (!firstSeen[id]) {
      firstSeen[id] = today;
    }

    const record = records.find(r => r.book_id === id);

    if (
      record &&
      record.completion_type === '当天新完结' &&
      !completedDetected[id]
    ) {
      completedDetected[id] = today;
    }
  }

  return {
    recordsById: Object.fromEntries(
      records.map(r => [r.book_id, r])
    ),

    nextState: {
      version: 1,
      last_successful_date: today,
      completed_ids: [...currentCompletedIds],
      ongoing_ids: [...currentOngoingIds],
      first_seen: firstSeen,
      completed_detected: completedDetected,
    },
  };
}

// ========== 主函数 ==========
async function main() {
  const now = getNowBJT();
  const today = fmtDate(now);

  console.log('='.repeat(68));
  console.log(`番茄小说完结作品追踪爬虫 - ${fmtDateTime(now)}`);
  console.log('='.repeat(68));

  ensureDir(DATA_DIR);
  ensureDir(HISTORY_DIR);

  const browser = await chromium.launch({
    headless: true,
    args: [
      '--no-sandbox',
      '--disable-setuid-sandbox',
      '--disable-blink-features=AutomationControlled',
    ],
  });

  let completedResult;
  let ongoingResult;

  try {
    completedResult = await crawlLibraryByPage(
      browser,
      COMPLETED_URL,
      '完结'
    );

    // stat1 是与 stat0 对应的连载状态页；
    // 如果站点路由调整，会保留旧快照而不误写状态。
    ongoingResult = await crawlLibraryByPage(
      browser,
      ONGOING_URL,
      '连载'
    );

  } finally {
    await browser.close().catch(() => {});
  }

  if (
    !completedResult ||
    !completedResult.books.length
  ) {
    throw new Error(
      '完结书库没有采集到数据；为避免覆盖有效数据，本次停止写入。'
    );
  }

  console.log('\n📊 获取分类映射...');

  const catGenderMap = await buildCategoryGenderMap();

  const previousState = readJson(STATE_PATH, null);

  const statusSnapshotReliable =
    completedResult.complete &&
    ongoingResult &&
    ongoingResult.complete;

  const tracking = classifyCompletion(
    completedResult.books,
    ongoingResult?.books || [],
    previousState,
    today
  );

  if (!previousState) {
    console.log(
      '  [提示] 首次运行：本次作为基准快照，不回溯真实完结日期。'
    );
  }

  if (
    !ongoingResult ||
    !ongoingResult.books.length ||
    !ongoingResult.complete
  ) {
    console.log(
      '  [WARN] 连载书库未能确认完整采集；本次不会更新状态快照，避免误判“当天新完结”。'
    );
  }

  if (!completedResult.complete) {
    console.log(
      '  [WARN] 完结书库未能确认完整采集；本次仍输出已采集结果，但不更新状态快照。'
    );
  }

  const previousRanks = readJson(
    path.join(DATA_DIR, 'latest.json'),
    null
  );

  const rawBooks = completedResult.books;
  const books = [];

  console.log(
    `\n📖 处理完结作品详情：${rawBooks.length} 本`
  );

  for (let i = 0; i < rawBooks.length; i++) {
    const raw = rawBooks[i];
    const id = String(raw.book_id);
    const rank = i + 1;

    let detail = {};

    try {
      const res = await withRetry(
        () => httpGet(`https://fanqienovel.com/page/${id}`),
        {
          name: `详情页 ${id}`,
          maxAttempts: 2,
          baseDelay: 1500,
        }
      );

      if (res.status >= 200 && res.status < 400) {
        detail = parseDetailPage(res.data);
      }

    } catch (e) {
      console.log(
        `  [WARN] 详情抓取失败 ${id}: ${e.message}`
      );
    }

    const bookName =
      raw.book_name ||
      detail.book_name ||
      `ID:${id}`;

    const author =
      raw.author ||
      detail.author ||
      '未知';

    const officialCategory = raw.category || '';

    const inferred = inferTags(
      bookName,
      detail.description || raw.abstract || ''
    );

    const officialTags = uniqueStrings([
      officialCategory,
      ...(detail.official_tags || []),
    ]).filter(t => t !== bookName && t !== author);

    const category =
      officialCategory ||
      (
        officialTags[0] ||
        inferCategoryFromText(
          bookName,
          detail.description || raw.abstract || ''
        ) ||
        '未分类'
      );

    const gender =
      catGenderMap[officialCategory]?.gender ||
      '未知';

    const completion =
      tracking.recordsById[id] || {
        completion_type: previousState ? '首次发现' : '基准快照',
        first_seen_date: today,
        completed_detected_date: null,
      };

    const allInferredTags = uniqueStrings([
      ...inferred.genre_tags,
      ...inferred.plot_tags,
      ...inferred.character_tags,
      ...inferred.setting_tags,
      ...inferred.style_tags,
    ]);

    const secondaryTags = uniqueStrings([
      ...officialTags,
      ...allInferredTags,
    ]).filter(t => t !== category);

    const allTags = uniqueStrings([
      category,
      ...secondaryTags,
    ]).filter(t => t !== '未分类');

    books.push({
      rank,
      book_id: id,
      book_name: bookName,
      author,
      gender,

      primary_tag: category,
      secondary_tags: secondaryTags,
      all_tags: allTags,

      official_tags: officialTags,
      genre_tags: inferred.genre_tags,
      plot_tags: inferred.plot_tags,
      character_tags: inferred.character_tags,
      setting_tags: inferred.setting_tags,
      style_tags: inferred.style_tags,
      inferred_tags: allInferredTags,

      abstract:
        detail.description ||
        raw.abstract ||
        '暂无简介',

      status: '完结',
      creation_status: raw.creation_status ?? 0,

      completion_type: completion.completion_type,
      first_seen_date: completion.first_seen_date,
      completed_detected_date: completion.completed_detected_date,

      last_chapter_time: raw.last_chapter_time || null,
      word_count: raw.word_count || null,
      read_count: raw.read_count || null,

      thumb_url:
        detail.hdImage ||
        raw.thumb_url ||
        '',

      book_url: `https://fanqienovel.com/page/${id}`,
      rank_change: null,
    });

    if ((i + 1) % 20 === 0) {
      console.log(
        `  已处理 ${i + 1}/${rawBooks.length}`
      );
    }

    if (i < rawBooks.length - 1) {
      await sleep(DETAIL_DELAY);
    }
  }

  // 排名变化：沿用项目原有逻辑
  console.log('\n📈 计算排名变化...');

  computeRankChange(
    books,
    DATA_DIR,
    today,
    'book_id'
  );

  const tagStats = {};
  const genderStats = {};
  const completionStats = {};

  for (const book of books) {
    const t = book.primary_tag;

    tagStats[t] = (tagStats[t] || 0) + 1;

    genderStats[book.gender] =
      (genderStats[book.gender] || 0) + 1;

    completionStats[book.completion_type] =
      (completionStats[book.completion_type] || 0) + 1;
  }

  const result = {
    update_time: fmtDateTime(now),
    update_date: today,
    total_count: books.length,

    source: '番茄小说书库·完结作品（按最新排序）',
    source_url: COMPLETED_URL,

    platform: 'fanqie',
    platform_name: '番茄小说',

    tag_stats: tagStats,
    gender_stats: genderStats,
    completion_stats: completionStats,

    crawl_info: {
      completed_pages_response_count:
        completedResult.responseCount,

      completed_has_more_false:
        completedResult.sawHasMoreFalse,

      completed_snapshot_complete:
        completedResult.complete,

      ongoing_pages_response_count:
        ongoingResult?.responseCount || 0,

      ongoing_has_more_false:
        ongoingResult?.sawHasMoreFalse || false,

      ongoing_snapshot_complete:
        Boolean(ongoingResult?.complete),

      status_snapshot_updated:
        Boolean(statusSnapshotReliable),
    },

    books,
  };

  writeJson(
    path.join(DATA_DIR, 'latest.json'),
    result
  );

  writeJson(
    path.join(HISTORY_DIR, `${today}.json`),
    result
  );

  // 独立完结追踪结果：方便前端只展示当天新增完结作品
  const newlyCompleted = books.filter(
    b => b.completion_type === '当天新完结'
  );

  const firstDiscovered = books.filter(
    b => b.completion_type === '首次发现'
  );

  const completionReport = {
    update_date: today,
    update_time: fmtDateTime(now),

    newly_completed_count: newlyCompleted.length,
    first_discovered_count: firstDiscovered.length,

    newly_completed: newlyCompleted,
    first_discovered: firstDiscovered,
  };

  writeJson(
    path.join(DATA_DIR, 'completed_today.json'),
    completionReport
  );

  // 仅在两个书库都采集可靠时更新状态快照
  if (statusSnapshotReliable) {
    writeJson(STATE_PATH, tracking.nextState);
  }

  // 更新历史索引
  const indexPath = path.join(DATA_DIR, 'history_index.json');

  let index = readJson(indexPath, []);

  if (!Array.isArray(index)) {
    index = [];
  }

  if (!index.includes(today)) {
    index.unshift(today);
  }

  index = index.slice(0, 90);

  writeJson(indexPath, index);

  // 完结追踪历史：按日期保存统计，不覆盖既有记录
  const completionHistory = readJson(
    COMPLETION_HISTORY_PATH,
    []
  );

  const historyArray = Array.isArray(completionHistory)
    ? completionHistory
    : [];

  const filteredHistory = historyArray.filter(
    item => item.date !== today
  );

  filteredHistory.unshift({
    date: today,
    completed_total: books.length,
    newly_completed: newlyCompleted.length,
    first_discovered: firstDiscovered.length,
    status_snapshot_updated: Boolean(statusSnapshotReliable),
  });

  writeJson(
    COMPLETION_HISTORY_PATH,
    filteredHistory.slice(0, 365)
  );

  console.log('\n' + '='.repeat(68));

  console.log(
    `🎉 本次完成：${books.length} 本完结作品`
  );

  console.log(
    `   当天新完结：${newlyCompleted.length} 本`
  );

  console.log(
    `   首次发现：${firstDiscovered.length} 本`
  );

  console.log(
    `   历史已收录：${completionStats['历史已收录'] || 0} 本`
  );

  console.log(
    `   状态快照：${statusSnapshotReliable ? '已更新' : '未更新（采集不完整）'}`
  );

  console.log(
    `   数据：${path.join(DATA_DIR, 'latest.json')}`
  );

  console.log(
    `   当日新增：${path.join(DATA_DIR, 'completed_today.json')}`
  );
}

main().catch(error => {
  console.error('\n❌ 爬虫执行失败：', error);

  console.error(
    '本次未将失败结果写入状态快照，避免污染历史数据。'
  );

  process.exit(1);
});
