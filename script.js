'use strict';
(() => {
  /* --- small compatibility shims (older Safari / Chrome / Samsung Internet) --- */
  if (!Element.prototype.replaceChildren) Element.prototype.replaceChildren = function () { while (this.firstChild) this.removeChild(this.firstChild); this.append.apply(this, arguments); };
  if (!window.CSS) window.CSS = {};
  if (!CSS.escape) CSS.escape = s => String(s).replace(/[^\w-]/g, ch => '\\' + ch);
  const HAS_INERT = 'inert' in HTMLElement.prototype;
  /* clickjacking guard: refuse to run inside someone else's frame when served over the web */
  if (/^https?:$/.test(location.protocol) && window.top !== window.self) { try { window.top.location.href = location.href; } catch (_) { document.documentElement.hidden = true; } return; }
  const $ = s => document.querySelector(s);
  const REDUCED = () => !!(window.matchMedia && matchMedia('(prefers-reduced-motion: reduce)').matches);

  /* =====================================================================
     Safe DOM helper: never uses innerHTML, never sets style / on* attributes
     ===================================================================== */
  const E = (tag, attrs = {}, ...kids) => {
    const el = document.createElement(tag);
    for (const [n, v] of Object.entries(attrs)) {
      if (v == null || v === false) continue;
      if (n === 'style' || /^on/i.test(n)) continue;
      if (n === 'class') el.className = v;
      else if (n === 'text') el.textContent = v;
      else el.setAttribute(n, v === true ? '' : String(v));
    }
    for (const k of kids) if (k != null && k !== false) el.append(k);
    return el;
  };
  const freeze = o => { if (o && typeof o === 'object' && !Object.isFrozen(o)) { Object.freeze(o); Object.values(o).forEach(freeze); } return o; };
  const COLORS = { '--pcm': 'pcm', '--pcb': 'pcb', '--com': 'com', '--hum': 'hum' };
  const colorOf = c => (COLORS[c] ? c : '--pcm');
  /* --c is the colour; --ct/--cm/--cb are static tints used when color-mix() is unavailable */
  const tint = (el, c) => {
    const k = COLORS[colorOf(c)];
    el.style.setProperty('--c', 'var(--' + k + ')');
    el.style.setProperty('--ct', 'var(--' + k + '-t)');
    el.style.setProperty('--cm', 'var(--' + k + '-m)');
    el.style.setProperty('--cb', 'var(--' + k + '-b)');
  };
  const years = y => (String(y) === '1' ? '1 year' : y + ' years');

  /* Debounce with cancel(); used with requestAnimationFrame for resize redraws */
  const debounce = (fn, ms) => {
    let t = 0;
    const w = (...a) => { clearTimeout(t); t = setTimeout(() => { t = 0; fn(...a); }, ms); };
    w.cancel = () => { clearTimeout(t); t = 0; };
    return w;
  };

  /* =====================================================================
     Fuzzy search: normalisation, synonym groups, typo tolerance (Damerau-Levenshtein)
     ===================================================================== */
  const norm = s => String(s || '').normalize('NFKD').replace(/[̀-ͯ]/g, '').toLowerCase().replace(/['’`´]/g, '').replace(/[^a-z0-9+#]+/g, ' ').trim();

  /* Each row is one concept. Typing any term finds items that mention any other term in the row.
     Terms shorter than 3 characters work as triggers only (they would be too noisy as expansions). */
  const SYN_GROUPS = [
    ['btech', 'b tech', 'be', 'bachelor of technology', 'engineering', 'engineer', 'engg'],
    ['mtech', 'm tech', 'me', 'master of technology', 'engineering', 'engg', 'gate'],
    ['mbbs', 'medicine', 'medical', 'doctor', 'physician', 'neet'],
    ['bds', 'dental', 'dentist', 'dentistry'],
    ['cs', 'cse', 'computer science', 'computing', 'software', 'it', 'coding', 'programming', 'developer'],
    ['ai', 'artificial intelligence', 'machine learning', 'ml', 'data science', 'data scientist'],
    ['bca', 'mca', 'computer applications'],
    ['law', 'llb', 'llm', 'legal', 'lawyer', 'advocate', 'clat'],
    ['mba', 'pgdm', 'management', 'business administration', 'cat'],
    ['ca', 'chartered accountant', 'accountant', 'accountancy', 'accounting'],
    ['bcom', 'mcom', 'commerce'],
    ['ba', 'ma', 'arts', 'humanities'],
    ['pilot', 'aviation', 'cpl', 'aircraft'],
    ['nursing', 'nurse', 'bsc nursing'],
    ['pharmacy', 'bpharm', 'mpharm', 'pharma', 'pharmacist'],
    ['architecture', 'barch', 'architect', 'nata'],
    ['design', 'designer', 'nid', 'nift', 'uceed', 'fashion'],
    ['bed', 'teaching', 'teacher', 'education'],
    ['journalism', 'journalist', 'media', 'mass communication', 'bjmc'],
    ['hotel', 'hospitality', 'bhm', 'hotel management'],
    ['agriculture', 'agri', 'farming', 'agronomy'],
    ['veterinary', 'vet', 'bvsc', 'animal'],
    ['psychology', 'psychologist', 'counselling', 'counseling'],
    ['bsc', 'msc', 'science'],
    ['physio', 'physiotherapy', 'bpt', 'physical therapy'],
    ['police', 'ips', 'upsc', 'civil services', 'ias'],
    ['army', 'defence', 'defense', 'nda', 'military'],
    ['cuet', 'cuet ug', 'cuet pg', 'central university'],
    ['jee', 'iit', 'nit'],
    ['finance', 'banking', 'financial'],
    ['data', 'analytics', 'statistics']
  ];
  const SYN = new Map();
  SYN_GROUPS.forEach((g, gi) => g.forEach(t => { const k = norm(t); if (!SYN.has(k)) SYN.set(k, new Set()); SYN.get(k).add(gi); }));
  const SYN_KEYS = [...SYN.keys()].filter(k => !k.includes(' '));
  const SYN_PHRASES = new Set([...SYN.keys()].filter(k => k.includes(' ')));

  /* Damerau-Levenshtein with early exit (distance, capped at k+1) */
  function editDistance(a, b, k) {
    const la = a.length, lb = b.length;
    if (Math.abs(la - lb) > k) return k + 1;
    if (a === b) return 0;
    let p2 = null, p1 = Array.from({ length: lb + 1 }, (_, j) => j);
    for (let i = 1; i <= la; i++) {
      const cur = [i]; let rowMin = i;
      for (let j = 1; j <= lb; j++) {
        let v = Math.min(p1[j] + 1, cur[j - 1] + 1, p1[j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
        if (p2 && i > 1 && j > 1 && a[i - 1] === b[j - 2] && a[i - 2] === b[j - 1]) v = Math.min(v, p2[j - 2] + 1);
        cur[j] = v; if (v < rowMin) rowMin = v;
      }
      if (rowMin > k) return k + 1;
      p2 = p1; p1 = cur;
    }
    return p1[lb];
  }
  /* allowed typos by token length: 1-3 chars exact, 4-5 one typo, 6+ two typos */
  const tolerance = n => (n < 4 ? 0 : n < 6 ? 1 : 2);

  function buildIndex(items, textFn, nameFn) {
    const docs = items.map(it => {
      const t = norm(textFn(it).join(' ')), nt = norm(nameFn(it).join(' '));
      return { t, pt: ' ' + t, c: t.replace(/ /g, ''), w: new Set(t.split(' ')), nw: new Set(nt.split(' ')) };
    });
    const vocab = [...new Set(docs.flatMap(d => [...d.w]))];
    return { docs, vocab, cache: new Map() };
  }

  /* synonym alternatives for one query token (exact or typo-tolerant match against the synonym keys) */
  function altsOf(tok) {
    const groups = new Set();
    if (SYN.has(tok)) SYN.get(tok).forEach(g => groups.add(g));
    else if (tok.length >= 5) { const k = tolerance(tok.length); for (const key of SYN_KEYS) if (key.length >= 5 && editDistance(tok, key, k) <= k) SYN.get(key).forEach(g => groups.add(g)); }
    const out = new Set();
    groups.forEach(g => SYN_GROUPS[g].forEach(t => { const n = norm(t); if (n !== tok && n.length >= 3) out.add(n); }));
    return [...out];
  }
  /* vocabulary words that are a typo (or a typo'd prefix) of the token */
  function fuzzyWords(ix, tok) {
    const hit = ix.cache.get(tok); if (hit) return hit;
    const k = tolerance(tok.length), found = new Set();
    if (k > 0) for (const w of ix.vocab) {
      if (editDistance(tok, w, k) <= k) found.add(w);
      else if (tok.length >= 5 && w.length > tok.length && editDistance(tok, w.slice(0, tok.length), 1) <= 1) found.add(w);
    }
    ix.cache.set(tok, found); return found;
  }
  /* exact / prefix / substring score of one string in one document, 0 when absent */
  function plainScore(a, d) {
    if (d.w.has(a)) return d.nw.has(a) ? 4.5 : 3;
    if (d.pt.includes(' ' + a)) return 2.4;
    if (a.length < 3) return 0;
    if (d.t.includes(a)) return 1.8;
    if (d.c.includes(a.replace(/ /g, ''))) return 1.5;
    return 0;
  }
  function tokenScore(ix, d, tok, alts, fz) {
    let best = plainScore(tok, d);
    for (const a of alts) { const s = plainScore(a, d) * 0.8; if (s > best) best = s; }
    if (best < 3 && fz.size) for (const w of fz) if (d.w.has(w)) { const s = d.nw.has(w) ? 2.2 : 1.2; if (s > best) best = s; }
    return best;
  }
  function queryTokens(q) {
    const t = q.split(' ').filter(Boolean).slice(0, 8), out = [];
    for (let i = 0; i < t.length; i++) {
      if (i + 1 < t.length && SYN_PHRASES.has(t[i] + ' ' + t[i + 1])) { out.push(t[i] + ' ' + t[i + 1]); i++; } else out.push(t[i]);
    }
    return out;
  }
  /* returns item indexes ranked best-first; every query token must match (directly, by synonym or by typo) */
  function fuzzySearch(ix, rawQuery) {
    const q = norm(rawQuery).slice(0, 70); if (!q) return [];
    const toks = queryTokens(q).map(tok => ({ tok, alts: altsOf(tok), fz: tok.includes(' ') ? new Set() : fuzzyWords(ix, tok) }));
    const res = [];
    ix.docs.forEach((d, i) => {
      let total = 0;
      for (const x of toks) { const s = tokenScore(ix, d, x.tok, x.alts, x.fz); if (!s) return; total += s; }
      res.push([i, total]);
    });
    return res.sort((a, b) => b[1] - a[1] || a[0] - b[0]).map(r => r[0]);
  }

  /* =====================================================================
     Data loading: async fetch, easy to swap for a database / API endpoint
     ===================================================================== */
  const DATA_URL = (document.querySelector('meta[name="roadmap-data"]') || {}).content || 'data.json';
  async function loadData(url = DATA_URL, timeoutMs = 15000) {
    const ctl = typeof AbortController === 'function' ? new AbortController() : null;
    const timer = ctl ? setTimeout(() => ctl.abort(), timeoutMs) : 0;
    try {
      const res = await fetch(url, { headers: { Accept: 'application/json' }, credentials: 'same-origin', cache: 'no-cache', signal: ctl ? ctl.signal : undefined });
      if (!res.ok) throw new Error('HTTP ' + res.status);
      const json = await res.json();
      return validate(json && !json.degrees && json.data ? json.data : json);   /* accepts {data:{...}} API envelopes too */
    } finally { clearTimeout(timer); }
  }
  function validate(db) {
    const arr = k => Array.isArray(db && db[k]) && db[k].length > 0;
    if (!['degrees', 'masters', 'streams', 'masterStreams'].every(arr)) throw new Error('Unexpected data shape');
    const ids = new Set([...db.degrees, ...db.masters].map(x => x && x.id));
    if (ids.size !== db.degrees.length + db.masters.length) throw new Error('Duplicate or missing ids');
    return db;
  }

  /* =====================================================================
     Theme and display mode (do not depend on data)
     ===================================================================== */
  const html = document.documentElement, THEME_KEY = 'india_roadmap_theme_v4';
  const dm = $('#darkBtn');
  const setTheme = (dark, save) => {
    html.setAttribute('data-theme', dark ? 'dark' : 'light');
    dm.setAttribute('aria-pressed', String(dark));
    dm.setAttribute('aria-label', dark ? 'Switch to light mode' : 'Switch to dark mode');
    dm.textContent = dark ? '☀️' : '🌙';
    const tc = document.querySelector('meta[name="theme-color"]'); if (tc) tc.setAttribute('content', dark ? '#09090d' : '#f5f7fb');
    if (save) { try { localStorage.setItem(THEME_KEY, dark ? '1' : '0'); } catch (_) { /* storage blocked */ } }
  };
  let savedTheme = null; try { savedTheme = localStorage.getItem(THEME_KEY); } catch (_) { /* ignore */ }
  setTheme(savedTheme === '1' || (savedTheme !== '0' && !!(window.matchMedia && matchMedia('(prefers-color-scheme: dark)').matches)), false);
  dm.addEventListener('click', () => setTheme(html.getAttribute('data-theme') !== 'dark', true));
  const tvBtn = $('#tvBtn');
  tvBtn.addEventListener('click', () => { const on = html.classList.toggle('tv'); tvBtn.setAttribute('aria-pressed', String(on)); });

  const status = $('#status'), toastEl = $('#toast');
  let toastT;
  const say = t => { status.textContent = ''; requestAnimationFrame(() => { status.textContent = t; }); };

  const toast = m => { say(m); toastEl.textContent = m; toastEl.hidden = false; clearTimeout(toastT); toastT = setTimeout(() => { toastEl.hidden = true; }, 3800); };
  const store = {
    get(k, d) { try { const v = localStorage.getItem(k); return v == null ? d : JSON.parse(v); } catch (_) { return d; } },
    set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (_) { /* storage blocked */ } },
    del(k) { try { localStorage.removeItem(k); } catch (_) { /* ignore */ } }
  };

  /* =====================================================================
     Scroll helpers: progress bar, back-to-top button with a progress ring, scroll reveal
     ===================================================================== */
  function setupScrollUi() {
    const bar = $('#prog i'), btn = $('#toTop'), ring = $('#toTopRing');
    let tick = false;
    const update = () => {
      tick = false;
      const y = window.pageYOffset || document.documentElement.scrollTop, max = Math.max(1, document.documentElement.scrollHeight - window.innerHeight);
      const p = Math.min(1, Math.max(0, y / max));
      bar.style.transform = 'scaleX(' + p.toFixed(4) + ')';
      ring.style.strokeDashoffset = String(100 - p * 100);
      btn.classList.toggle('show', y > 360);
    };
    const onScroll = () => { if (!tick) { tick = true; requestAnimationFrame(update); } };
    addEventListener('scroll', onScroll, { passive: true });
    addEventListener('resize', onScroll, { passive: true });
    btn.addEventListener('click', () => {
      try { window.scrollTo({ top: 0, behavior: REDUCED() ? 'auto' : 'smooth' }); } catch (_) { window.scrollTo(0, 0); }
      btn.blur();
    });
    update();
  }
  function setupReveal() {
    const els = [...document.querySelectorAll('.card, .map, .legal')];
    if (!('IntersectionObserver' in window) || REDUCED()) return;
    html.classList.add('anim');
    els.forEach((el, i) => { el.classList.add('reveal'); el.style.transitionDelay = Math.min(i % 4, 3) * 80 + 'ms'; });
    const io = new IntersectionObserver(es => es.forEach(e => {
      if (!e.isIntersecting) return;
      e.target.classList.add('in'); io.unobserve(e.target);
      setTimeout(() => { e.target.style.transitionDelay = ''; }, 1200);
    }), { threshold: 0.06, rootMargin: '0px 0px -5% 0px' });
    els.forEach(el => io.observe(el));
    /* safety net: never leave content hidden */
    setTimeout(() => els.forEach(el => el.classList.add('in')), 6000);
  }
  function celebrate() {
    if (REDUCED()) return;
    const cols = ['#7b9cff', '#34d9c3', '#f7b04a', '#f77fbd', '#4ade80'];
    for (let i = 0; i < 26; i++) {
      const c = E('i', { class: 'confetti', 'aria-hidden': 'true' });
      const a = Math.random() * Math.PI * 2, d = 90 + Math.random() * 190;
      c.style.background = cols[i % cols.length];
      c.style.setProperty('--x', Math.round(Math.cos(a) * d) + 'px');
      c.style.setProperty('--y', Math.round(Math.sin(a) * d - 60 + 160) + 'px');
      c.style.setProperty('--rot', Math.round(Math.random() * 720 - 360) + 'deg');
      document.body.append(c); setTimeout(() => c.remove(), 1500);
    }
  }

  /* =====================================================================
     Boot: load data, then build the app
     ===================================================================== */
  const main = $('#main'), stateBox = $('#state'), splash = $('#splash'), tipEl = $('#spTip');
  const TIPS = ['Tap any degree to see which master\'s routes usually follow it.', 'Compare as many degrees as you like, side by side.', 'Try searching "btech", "doctor" or "NEET". Small typos are fine.', 'Not sure where to start? Pick your 12th stream and explore.', 'Your explored pathways are remembered on this device.'];
  let tipI = 0, tipT = 0, started = false;
  const rotateTips = () => { if (!tipEl) return; tipEl.textContent = TIPS[0]; tipT = setInterval(() => { tipEl.classList.add('swap'); setTimeout(() => { tipI = (tipI + 1) % TIPS.length; tipEl.textContent = TIPS[tipI]; tipEl.classList.remove('swap'); }, 350); }, 2200); };
  const hideSplash = () => { clearInterval(tipT); splash.classList.add('done'); splash.setAttribute('aria-hidden', 'true'); setTimeout(() => { splash.hidden = true; }, 800); };
  const wait = ms => new Promise(r => setTimeout(r, ms));
  async function boot() {
    const t0 = Date.now();
    main.classList.add('app-loading'); stateBox.hidden = true;
    if (splash.hidden) { splash.hidden = false; splash.classList.remove('done'); splash.removeAttribute('aria-hidden'); }
    if (!tipT) rotateTips();
    try {
      const db = freeze(await loadData());
      if (started) return;
      started = true;
      start(db);
      main.classList.remove('app-loading');
      await wait(Math.max(0, (REDUCED() ? 250 : 1500) - (Date.now() - t0)));   /* let the loading animation play once */
      hideSplash();
      setupReveal();
      setTimeout(() => flowB.intro(), 450);
    } catch (err) {
      hideSplash();
      const retry = E('button', { class: 'qbtn', type: 'button', text: 'Try again' });
      retry.addEventListener('click', boot);
      const offline = location.protocol === 'file:';
      stateBox.replaceChildren(
        E('p', { text: 'Sorry, the roadmap data could not be loaded.' }),
        E('p', { class: 'fine', text: offline ? 'This page fetches data.json, so it needs to be opened through a web server (not directly from a file).' : 'Please check your connection and try again.' }),
        retry);
      stateBox.hidden = false;
    }
  }

  let flowB, flowM;   /* assigned in start() */

  function start(DB) {
    const DEG = DB.degrees, MAS = DB.masters, ST = DB.streams, MST = DB.masterStreams;
    const PROG = DB.prog || {}, NOTES = DB.notes || {}, UPDATED = DB.updated || '';
    const DG = new Map(DEG.map(d => [d.id, d])), MG = new Map(MAS.map(m => [m.id, m]));
    const REV = new Map();
    for (const [d, ms] of Object.entries(PROG)) for (const m of ms) { if (!MG.has(m) || !DG.has(d)) continue; if (!REV.has(m)) REV.set(m, []); REV.get(m).push(d); }
    const streamsOf = id => ST.map((_, i) => i).filter(i => ST[i].cats.some(c => c.ids.includes(id)));
    const mstreamsOf = id => MST.map((_, i) => i).filter(i => MST[i].cats.some(c => c.ids.includes(id)));
    const NOTICE = 'Salary (LPA) and demand are indicative estimates, not guarantees. Eligibility, duration and entrance exams change every year, so confirm on the official NTA, university, regulator or professional-body notice before applying.' + (UPDATED ? ' Updated ' + UPDATED + '.' : '');
    const ELIG_NOTE = DB.eligNote || 'Eligibility follows general UGC/AICTE national norms; specific university rules apply.';

    /* ---------- journey: remembers what you explored (retention) ---------- */
    const SEEN_KEY = 'india_roadmap_seen_v1', RECENT_KEY = 'india_roadmap_recent_v1';
    const known = id => DG.has(id) || MG.has(id);
    const strs = v => (Array.isArray(v) ? v.filter(x => typeof x === 'string') : []);
    const SEEN = new Set(strs(store.get(SEEN_KEY, [])).filter(known));
    let RECENT = strs(store.get(RECENT_KEY, [])).filter(known).slice(0, 6);
    const TOTAL = DEG.length + MAS.length;
    const LEVELS = [[0, 'Starter', 'Tap any card to begin your journey.'], [1, 'Curious', 'Great start! Every pathway you open is remembered.'], [5, 'Explorer', 'You are getting a feel for the landscape.'], [15, 'Pathfinder', 'Impressive range. Try comparing a few of them side by side.'], [30, 'Trailblazer', 'You have covered serious ground.'], [60, 'Roadmap master', 'Few people explore this much. You know the map.'], [100, 'Legend', 'You have seen almost everything here.']];
    const MILESTONES = new Set([1, 5, 15, 30, 60, 100]);
    const nameOf = id => (DG.get(id) || MG.get(id) || {}).n || id;
    function renderJourney() {
      const box = $('#journey'); if (!SEEN.size) { box.hidden = true; return; }
      box.hidden = false;
      const n = SEEN.size, pct = Math.min(100, Math.round(n / TOTAL * 100));
      let lv = LEVELS[0]; for (const l of LEVELS) if (n >= l[0]) lv = l;
      $('#jRing').style.strokeDashoffset = String(100 - Math.max(pct, 3));
      $('#jPct').textContent = pct + '%';
      $('#jLvl').textContent = lv[1];
      $('#jMsg').textContent = 'You have explored ' + n + ' of ' + TOTAL + ' pathways.';
      $('#jSub').textContent = lv[2];
      const rc = $('#jRecent');
      rc.replaceChildren(...RECENT.map(id => chip(nameOf(id), () => openView(() => (DG.has(id) ? degreeView(id) : masterView(id))))));
      $('#jRecentT').hidden = rc.hidden = !RECENT.length;
    }
    function markSeen(id) {
      RECENT = [id, ...RECENT.filter(x => x !== id)].slice(0, 6);
      store.set(RECENT_KEY, RECENT);
      if (!SEEN.has(id)) {
        SEEN.add(id); store.set(SEEN_KEY, [...SEEN]);
        document.querySelectorAll('[data-d="' + CSS.escape(id) + '"]').forEach(el => el.classList.add('seen'));
        if (MILESTONES.has(SEEN.size) && SEEN.size > 1) { celebrate(); const lv = LEVELS.filter(l => SEEN.size >= l[0]).pop(); toast('🎉 Level up: ' + lv[1] + '! ' + SEEN.size + ' pathways explored.'); }
      }
      renderJourney();
    }
    $('#jReset').addEventListener('click', () => {
      if (!window.confirm('Reset your exploration journey on this device?')) return;
      SEEN.clear(); RECENT = []; store.del(SEEN_KEY); store.del(RECENT_KEY);
      document.querySelectorAll('.row.seen').forEach(el => el.classList.remove('seen')); renderJourney(); say('Journey reset');
    });

    /* ---------- dialog manager (single dialog, in-dialog navigation with Back) ---------- */
    const dlg = $('#dlg'), back = $('#back'), tray = $('#tray');
    const cmp = new Set();            /* no upper limit */
    let trail = [], openFrom = null;
    const isOpen = () => dlg.classList.contains('open');
    const syncTray = () => {
      tray.hidden = isOpen() || cmp.size === 0;
      document.body.classList.toggle('has-tray', !tray.hidden);
      $('#cmpCount').textContent = cmp.size + (cmp.size === 1 ? ' degree' : ' degrees') + ' selected';
      $('#cmpGo').disabled = cmp.size < 2;
    };
    const cmpLabel = (b, id) => {
      const on = cmp.has(id), n = (DG.get(id) || {}).n || id;
      b.setAttribute('aria-pressed', String(on));
      b.setAttribute('aria-label', (on ? 'Remove ' : 'Add ') + n + (on ? ' from comparison' : ' to comparison'));
      b.textContent = on ? '×' : '+';
    };
    const syncCmpUi = () => document.querySelectorAll('[data-cmp]').forEach(b => cmpLabel(b, b.getAttribute('data-cmp')));
    function toggleCmp(id) {
      const n = (DG.get(id) || {}).n || id;
      if (cmp.has(id)) { cmp.delete(id); say('Removed ' + n + ' from comparison. ' + cmp.size + ' selected.'); }
      else { cmp.add(id); say('Added ' + n + ' to comparison. ' + cmp.size + ' selected.'); }
      syncCmpUi(); syncTray();
    }
    function renderView(v) {
      const bar = E('div', { class: 'dbar' });
      if (trail.length > 1) {
        const bk = E('button', { class: 'qbtn', type: 'button', text: '← Back' });
        bk.addEventListener('click', () => { trail.pop(); renderView(trail[trail.length - 1]()); });
        bar.append(bk);
      }
      const x = E('button', { class: 'x', type: 'button', 'aria-label': 'Close dialog', text: '×' });
      x.addEventListener('click', () => closeDlg());
      bar.append(x);
      dlg.classList.toggle('wide', !!v.wide);
      dlg.replaceChildren(bar, ...v.nodes);
      dlg.setAttribute('aria-labelledby', 'dlgTitle');
      dlg.scrollTop = 0;
      const t = dlg.querySelector('#dlgTitle');
      if (t) setTimeout(() => t.focus({ preventScroll: true }), 40);
    }
    function openView(build, from) {
      if (!isOpen()) {
        trail = []; openFrom = from || document.activeElement;
        main.inert = true; dlg.inert = false;
        if (!HAS_INERT) main.setAttribute('aria-hidden', 'true');
        dlg.classList.add('open'); back.classList.add('open'); html.classList.add('lock');
        syncTray();
      }
      trail.push(build);
      renderView(build());
    }
    function closeDlg(restore = true) {
      if (!isOpen()) return;
      const from = openFrom; trail = []; openFrom = null;
      dlg.classList.remove('open', 'wide'); back.classList.remove('open'); html.classList.remove('lock');
      dlg.inert = true; main.inert = false; if (!HAS_INERT) main.removeAttribute('aria-hidden'); syncTray();
      if (restore && from && from.isConnected) from.focus({ preventScroll: true });
    }
    back.addEventListener('click', () => closeDlg());
    addEventListener('keydown', e => {
      if (e.key === 'Escape') closeDlg();
      if (e.key === 'Tab' && isOpen() && !HAS_INERT) {   /* focus trap for browsers without inert */
        const f = [...dlg.querySelectorAll('button, [href], input, select, summary, [tabindex]:not([tabindex="-1"])')].filter(x => !x.disabled && x.offsetParent !== null);
        if (!f.length) return;
        const first = f[0], last = f[f.length - 1];
        if (e.shiftKey && (document.activeElement === first || !dlg.contains(document.activeElement))) { e.preventDefault(); last.focus(); }
        else if (!e.shiftKey && document.activeElement === last) { e.preventDefault(); first.focus(); }
      }
    });

    /* ---------- view helpers ---------- */
    const ccard = (t, ...k) => E('section', { class: 'ccard' }, E('h4', { text: t }), ...k);
    const chip = (label, fn, c) => { const b = E('button', { class: 'chip' + (c ? '' : ' plain'), type: 'button', text: label }); if (c) tint(b, c); b.addEventListener('click', fn); return b; };

    /* ----- structured detail layout: hero header, key-fact tiles, titled sections ----- */
    const splitTop = str => { const out = []; let depth = 0, cur = ''; for (const ch of String(str || '')) { if (ch === '(') depth++; if (ch === ')') depth = Math.max(0, depth - 1); if (ch === ',' && !depth) { out.push(cur.trim()); cur = ''; } else cur += ch; } if (cur.trim()) out.push(cur.trim()); return out; };
    const sec = (icon, title, ...kids) => E('section', { class: 'dsec' }, E('h3', {}, E('span', { class: 'ic', 'aria-hidden': 'true', text: icon }), title), ...kids);
    const fact = (label, value) => E('div', { class: 'fact' }, E('h5', { text: label }), E('p', { text: value }));
    const factBox = (...f) => E('div', { class: 'factbox' }, ...f.filter(Boolean));
    const pills = str => E('ul', { class: 'pills' }, ...splitTop(str).map(x => E('li', { text: x })));
    const tile = (icon, value, label) => E('div', { class: 'tile' }, E('span', { class: 'ti', 'aria-hidden': 'true', text: icon }), E('b', { text: value }), E('small', { text: label }));
    const head = (title, full, badges, color, tiles) => {
      const h = E('header', { class: 'dhead' }, E('div', { class: 'badges' }, ...badges), E('h2', { id: 'dlgTitle', tabindex: '-1', text: title }), E('p', { class: 'full', text: full }));
      tint(h, color); return [h, E('div', { class: 'tiles' }, ...tiles)];
    };

    function degreeView(id) {
      const d = DG.get(id), prog = (PROG[id] || []).filter(mid => MG.has(mid));
      markSeen(id);
      const sIdx = streamsOf(id);
      const cb = E('button', { class: 'qbtn', type: 'button', 'data-cmp': id });
      const cbRefresh = () => { const on = cmp.has(id); cb.setAttribute('aria-pressed', String(on)); cb.textContent = on ? 'In comparison (remove)' : '+ Compare this degree'; cb.setAttribute('aria-label', (on ? 'Remove ' : 'Add ') + d.n + (on ? ' from comparison' : ' to comparison')); };
      cbRefresh();
      cb.addEventListener('click', () => { toggleCmp(id); cbRefresh(); });
      const nodes = [
        ...head(d.n, d.full, [E('span', { class: 'badge', text: d.type }), d.kind === 'pathway' && E('span', { class: 'badge warn', text: 'Not a standard bachelor\'s degree' })], (ST[sIdx[0]] || {}).c,
          [tile('⏱️', years(d.yrs), 'Duration'), tile('🎓', d.kind === 'pathway' ? 'Pathway' : 'Degree', 'Level'), tile('🧭', String(sIdx.length), sIdx.length === 1 ? 'Stream' : 'Streams'), tile('➡️', String(prog.length), 'Next steps')]),
        sec('📋', 'Eligibility & admission', factBox(fact('10+2 eligibility', d.elig), fact('Entrance / selection', d.exam))),
        sec('🏛️', 'Where to study', pills(d.institutes)),
        sec('📈', 'Career & outlook', E('div', { class: 'grid' },
          ccard('Demand & opportunities', E('p', { text: d.demand }), E('p', { text: 'Pathways: ' + d.path })),
          ccard('Indicative salary in India', E('p', { class: 'salary', text: d.pay })),
          ccard('Why pursue this?', E('p', { text: d.why })),
          NOTES[id] && ccard('Good to know', E('p', { text: NOTES[id] })))),
        sec('❓', 'Questions students often ask',
          E('div', { class: 'qa' },
            E('details', { open: '' }, E('summary', { text: 'Which Class 12 subjects and entrance exam do I need?' }), E('p', { text: d.elig + ' Selection route: ' + d.exam })),
            E('details', {}, E('summary', { text: 'What can I realistically earn and do afterwards?' }), E('p', { text: 'Indicative entry pay: ' + d.pay + ' Typical roles: ' + d.path + ' ' + d.demand })),
            E('details', {}, E('summary', { text: 'Which streams can apply?' }), E('p', { text: 'Listed under: ' + sIdx.map(i => ST[i].n).join(', ') + '. Always check the subject prerequisites in the official prospectus.' })),
            (d.kind === 'degree' && /^[34]/.test(d.yrs)) ? E('details', {}, E('summary', { text: 'How does this connect to a Master\'s under NEP 2020?' }), E('p', { text: 'After a 3-year bachelor\'s you usually join a 2-year Master\'s. A 4-year Honours / Research degree may make you eligible for a 1-year Master\'s or direct PhD entry at many universities (the UGC norm is about 75% aggregate). Rules vary by university.' })) : null)),
      ];
      if (prog.length) nodes.push(sec('➡️', 'Typical next steps: Master\'s & PG options', E('div', { class: 'chips' }, ...prog.map(mid => chip(MG.get(mid).n, () => openView(() => masterView(mid)), (MST[mstreamsOf(mid)[0]] || {}).c)))));
      nodes.push(sec('🗺️', d.kind === 'pathway' ? 'Listed under (tap to see it in the map)' : 'Open to students from (tap to see it in the map)',
        E('div', { class: 'chips' }, ...sIdx.map(i => chip(ST[i].e + ' ' + ST[i].n, () => { closeDlg(false); showTab(0); flowB.go(i, id); }, ST[i].c)))),
        sec('⚖️', 'Compare with other degrees', E('div', { class: 'chips' }, cb)),
        d.cbseRef && E('p', { class: 'ref' }, E('b', { text: 'Compendium reference: ' }), d.cbseRef),
        E('p', { class: 'note', text: NOTICE }));
      return { nodes };
    }

    function masterView(id) {
      const m = MG.get(id), routes = (REV.get(id) || []).filter(did => DG.has(did)), sIdx = mstreamsOf(id);
      markSeen(id);
      const nodes = [
        ...head(m.n, m.full, [E('span', { class: 'badge', text: m.f }), m.varies && E('span', { class: 'badge warn', text: 'University rules vary' })], (MST[sIdx[0]] || {}).c,
          [tile('⏱️', m.dur, 'Duration'), tile('📚', m.f, 'Field'), tile('🏛️', m.varies ? 'Varies' : 'Standard', 'University rules'), tile('🎓', String(routes.length), 'Bachelor\'s routes')]),
        sec('📋', 'Eligibility & admission', factBox(fact(m.varies ? 'Eligibility (UGC/AICTE norms; university rules apply)' : 'Eligibility', m.elig), fact('Entrance / selection', m.exam))),
        sec('🏛️', 'Where to study', pills(m.institutes)),
        sec('📈', 'Career & outlook', E('div', { class: 'grid' },
          ccard('Demand & opportunities', E('p', { text: m.demand }), E('p', { text: 'Typical pathways: ' + m.paths })),
          ccard('Indicative salary in India', E('p', { class: 'salary', text: m.salary })),
          ccard('Why pursue this?', E('p', { text: m.why })))),
        sec('❓', 'Questions students often ask', E('div', { class: 'qa' },
          E('details', { open: '' }, E('summary', { text: 'Which bachelor\'s degrees make me eligible?' }), E('p', { text: m.elig })),
          E('details', {}, E('summary', { text: 'What is the entrance route and post-PG pay?' }), E('p', { text: 'Entrance: ' + m.exam + ' Indicative pay: ' + m.salary + ' Career paths: ' + m.paths })))),
      ];
      if (routes.length) nodes.push(sec('🎓', 'Common bachelor\'s routes into this', E('div', { class: 'chips' }, ...routes.map(did => chip(DG.get(did).n, () => openView(() => degreeView(did)), ST[streamsOf(did)[0]] && ST[streamsOf(did)[0]].c)))));
      if (sIdx.length) nodes.push(sec('🗺️', 'Show it in the Master\'s map', E('div', { class: 'chips' }, ...sIdx.map(i => chip(MST[i].e + ' ' + MST[i].n, () => { closeDlg(false); showTab(1); flowM.go(i, id); }, MST[i].c)))));
      if (m.cbseRef) nodes.push(E('p', { class: 'ref' }, E('b', { text: 'Reference: ' }), m.cbseRef));
      nodes.push(E('p', { class: 'note', text: ELIG_NOTE + ' ' + NOTICE }));
      return { nodes };
    }

    function compareView() {
      const L = [...cmp].map(id => DG.get(id)).filter(Boolean);
      const R = [['Full name', d => d.full], ['Type', d => d.type], ['Duration', d => years(d.yrs)], ['10+2 eligibility', d => d.elig], ['Entrance', d => d.exam], ['Indicative salary', d => d.pay], ['Demand', d => d.demand], ['Pathways', d => d.path], ['Key institutes', d => d.institutes], ['Open to', d => streamsOf(d.id).map(i => ST[i].n).join(', ')], ['Next steps', d => (PROG[d.id] || []).filter(m => MG.has(m)).map(m => MG.get(m).n).join(', ') || 'Not mapped']];
      const heads = L.map(d => {
        const rm = E('button', { class: 'rm', type: 'button', text: 'Remove', 'aria-label': 'Remove ' + d.n + ' from comparison' });
        rm.addEventListener('click', () => {
          const w = dlg.querySelector('.cmpwrap'), sl = w ? w.scrollLeft : 0;
          toggleCmp(d.id);
          if (!cmp.size) { closeDlg(); return; }
          renderView(compareView());
          const w2 = dlg.querySelector('.cmpwrap'); if (w2) { w2.style.scrollBehavior = 'auto'; w2.scrollLeft = sl; w2.style.scrollBehavior = ''; }
        });
        return E('th', { scope: 'col' }, d.n, rm);
      });
      const t = E('table', { class: 'cmp' }, E('thead', {}, E('tr', {}, E('th', { scope: 'col', text: 'Feature' }), ...heads)),
        E('tbody', {}, ...R.map(([k, f]) => E('tr', {}, E('th', { scope: 'row', text: k }), ...L.map(d => E('td', { text: f(d) }))))));
      return { wide: true, nodes: [E('h2', { id: 'dlgTitle', tabindex: '-1', text: 'Compare degrees (' + L.length + ')' }),
        L.length > 3 && E('p', { class: 'note', text: 'Scroll sideways (or use the arrow keys inside the table) to see all ' + L.length + ' degrees.' }),
        E('div', { class: 'cmpwrap', tabindex: '0', role: 'region', 'aria-label': 'Comparison table, scrolls horizontally' }, t), E('p', { class: 'note', text: NOTICE })] };
    }
    $('#cmpGo').addEventListener('click', e => openView(compareView, e.currentTarget));
    $('#cmpClear').addEventListener('click', () => { cmp.clear(); syncCmpUi(); syncTray(); say('Comparison cleared'); });

    /* =====================================================================
       Flow map engine (animated web of SVG connectors; used by both maps)
       ===================================================================== */
    const NS = 'http://www.w3.org/2000/svg';
    function createFlow(cfg) {
      const { map, svg, rootEl, box, panel, hint, items, rowFor, unit, noun } = cfg;
      let cur = -1, loaded = false, busyUntil = 0, pendingFocus = null, pt, raf = 0, lastW = 0, lastH = 0;
      const total = s => s.cats.reduce((n, c) => n + c.ids.length, 0);
      const rel = el => { let x = 0, y = 0; while (el && el !== map) { x += el.offsetLeft; y += el.offsetTop; el = el.offsetParent; } return { x, y }; };
      const path = (d, c, delay, w, o, still) => {
        const p = document.createElementNS(NS, 'path');
        p.setAttribute('d', d); p.setAttribute('pathLength', '1'); if (still) p.setAttribute('class', 's');
        p.style.stroke = 'var(' + colorOf(c) + ')'; p.style.strokeWidth = w; p.style.opacity = o; p.style.animationDelay = delay + 'ms';
        return p;
      };
      const busy = ms => { busyUntil = performance.now() + ms; };

      const btns = items.map((s, i) => {
        const b = E('button', { class: 'st', type: 'button', 'aria-expanded': 'false', 'aria-controls': panel.id },
          E('span', { class: 'em', text: s.e }), E('b', { text: s.n }), E('small', { text: s.sub }), E('span', { class: 'act' }));
        tint(b, s.c); b.style.animationDelay = (200 + i * 110) + 'ms';
        b.addEventListener('click', () => pick(i));
        b.addEventListener('keydown', e => {
          const k = { ArrowRight: i + 1, ArrowLeft: i - 1, Home: 0, End: items.length - 1 }[e.key];
          if (k == null) return; e.preventDefault(); btns[(k + items.length) % items.length].focus();
        });
        box.append(b); return b;
      });
      const labels = () => btns.forEach((b, j) => {
        const on = j === cur;
        b.classList.toggle('sel', on); b.setAttribute('aria-expanded', String(on));
        b.querySelector('.act').textContent = on ? 'Expanded · tap to collapse' : total(items[j]) + ' ' + unit + ' · tap to explore';
      });
      labels();

      function draw(animate, branches) {
        const W = map.clientWidth; if (!W) return;
        const H = map.offsetHeight, out = [];
        lastW = W; lastH = H;
        svg.setAttribute('viewBox', '0 0 ' + W + ' ' + H); svg.style.height = H + 'px';
        const r = rel(rootEl), rx = r.x + rootEl.offsetWidth / 2, ry = r.y + rootEl.offsetHeight;
        btns.forEach((b, i) => {
          const p = rel(b), x = p.x + b.offsetWidth / 2, on = i === cur;
          out.push(path('M' + rx + ' ' + ry + 'C' + rx + ' ' + (ry + 30) + ' ' + x + ' ' + (p.y - 30) + ' ' + x + ' ' + p.y, items[i].c, 300 + i * 110, on ? 4 : 2.5, cur < 0 || on ? 1 : 0.4, loaded));
        });
        if (branches && cur >= 0) {
          const b = btns[cur], p = rel(b), sx = p.x + b.offsetWidth / 2, sy = p.y + b.offsetHeight;
          const g = Math.max(8, rel(panel).x - 12), hs = [...panel.querySelectorAll('h3')], c = items[cur].c;
          if (hs.length) {
            const ys = hs.map(t => rel(t).y + t.offsetHeight / 2);
            out.push(path('M' + sx + ' ' + sy + 'C' + sx + ' ' + (sy + 22) + ' ' + g + ' ' + (sy + 4) + ' ' + g + ' ' + (sy + 34) + 'L' + g + ' ' + ys[ys.length - 1], c, 150, 3, 1, !animate));
            hs.forEach((t, i) => out.push(path('M' + g + ' ' + (ys[i] - 12) + 'Q' + g + ' ' + ys[i] + ' ' + (g + 12) + ' ' + ys[i] + 'L' + rel(t).x + ' ' + ys[i], c, 450 + i * 110, 3, 1, !animate)));
          }
        }
        svg.replaceChildren(...out); loaded = true;
      }

      function render() {
        const s = items[cur]; if (!s) return;
        tint(panel, s.c);
        const col = E('button', { class: 'qbtn', type: 'button', text: 'Collapse ' + s.n + ' ×' });
        col.addEventListener('click', collapse);
        const bar = E('div', { class: 'bar' }, E('b', { text: s.e + ' ' + s.n + ': ' + total(s) + ' ' + noun }), col);
        const cats = s.cats.map((c, i) => {
          const sec = E('section', { class: 'cat' }, E('h3', {}, E('span', { 'aria-hidden': 'true', text: c.e }), c.t, E('small', { text: '(' + c.ids.length + ')' })),
            E('ul', {}, ...c.ids.map((id, j) => { const w = rowFor(id); if (!w) return null; const li = E('li', {}, w); li.style.setProperty('--j', j); return li; })));
          sec.style.setProperty('--i', i); return sec;
        });
        panel.replaceChildren(bar, ...cats);
        panel.classList.remove('out');
        syncCmpUi();
        say(s.n + ': ' + total(s) + ' ' + noun);
      }

      function focusRow(id) {
        const t = panel.querySelector('[data-d="' + CSS.escape(id) + '"]'); if (!t) return;
        t.scrollIntoView({ behavior: REDUCED() ? 'auto' : 'smooth', block: 'center' });
        t.classList.remove('pulse'); void t.offsetWidth; t.classList.add('pulse');
        setTimeout(() => t.classList.remove('pulse'), 1900);
        t.focus({ preventScroll: true });
      }

      function collapse() {
        clearTimeout(pt); cur = -1; labels(); panel.classList.remove('out'); map.classList.remove('has');
        hint.hidden = false; panel.replaceChildren(); draw(false, false); say('Collapsed back to the stream boxes');
      }
      function pick(i) {
        if (i === cur) { collapse(); return; }
        const had = cur >= 0; cur = i; labels();
        map.classList.add('has'); hint.hidden = true; panel.classList.add('out'); draw(false, false);
        clearTimeout(pt);
        pt = setTimeout(() => {
          if (cur !== i) return;
          render();
          requestAnimationFrame(() => {
            draw(true, true); busy(1400 + items[i].cats.length * 120);
            rootEl.scrollIntoView({ behavior: REDUCED() ? 'auto' : 'smooth', block: 'start' });
            if (pendingFocus) { const id = pendingFocus; pendingFocus = null; setTimeout(() => focusRow(id), 700); }
          });
        }, had ? 200 : 0);
      }
      function go(i, id) {
        if (i === cur) { focusRow(id); return; }
        pendingFocus = id; pick(i);
      }
      function intro() { if (!loaded && map.clientWidth) { draw(true, false); busy(1300); } }

      /* Resize handling: requestAnimationFrame keeps the lines glued to the layout while the window is being
         dragged (at most one redraw per frame); a trailing debounce then guarantees one exact final redraw,
         and waits for any running entrance animation first so it is never cut short. */
      const frame = () => { raf = 0; draw(false, cur >= 0); };
      const queueFrame = () => { if (!raf) raf = requestAnimationFrame(frame); };
      const settle = debounce(() => {
        if (performance.now() < busyUntil) { settle(); return; }
        if (raf) { cancelAnimationFrame(raf); raf = 0; }
        draw(false, cur >= 0);
      }, 120);
      function redraw() {
        if (!map.clientWidth) return;                       /* hidden tab: nothing to measure */
        if (performance.now() >= busyUntil) queueFrame();  /* live snap during the resize */
        settle();                                           /* exact redraw once the resize stops */
      }
      if ('ResizeObserver' in window) {
        new ResizeObserver(entries => {
          const r = entries[0] && entries[0].contentRect;
          if (r && Math.round(r.width) === lastW && Math.round(r.height) === lastH) return;   /* ignore no-op notifications */
          redraw();
        }).observe(map);
      } else addEventListener('resize', redraw);
      return { pick, go, intro, redraw };
    }

    /* rows */
    const degreeRow = d => {
      const b = E('button', { class: 'row' + (SEEN.has(d.id) ? ' seen' : ''), type: 'button', 'data-d': d.id },
        E('span', { class: 'degree-copy' }, E('b', { text: d.n }), d.kind === 'pathway' && E('span', { class: 'badge warn', text: d.type }), E('span', { class: 'desc', text: d.desc })),
        E('i', { text: years(d.yrs) }));
      b.addEventListener('click', () => openView(() => degreeView(d.id), b));
      const q = E('button', { class: 'qbtn cmpbtn', type: 'button', 'data-cmp': d.id });
      cmpLabel(q, d.id); q.addEventListener('click', () => toggleCmp(d.id));
      return E('div', { class: 'rwrap' }, b, q);
    };
    const masterRow = m => {
      const b = E('button', { class: 'row' + (SEEN.has(m.id) ? ' seen' : ''), type: 'button', 'data-d': m.id },
        E('span', { class: 'degree-copy' }, E('b', { text: m.n }), E('span', { class: 'desc', text: m.full })), E('i', { text: m.dur }));
      b.addEventListener('click', () => openView(() => masterView(m.id), b));
      return E('div', { class: 'rwrap' }, b);
    };
    flowB = createFlow({ map: $('#map'), svg: $('#web'), rootEl: $('#root'), box: $('#streams'), panel: $('#panel'), hint: $('#hint'), items: ST, rowFor: id => DG.has(id) ? degreeRow(DG.get(id)) : null, unit: 'pathways', noun: 'options' });
    flowM = createFlow({ map: $('#mMap'), svg: $('#mWeb'), rootEl: $('#mRoot'), box: $('#mStreams'), panel: $('#mPanel'), hint: $('#mHint'), items: MST, rowFor: id => MG.has(id) ? masterRow(MG.get(id)) : null, unit: 'PG routes', noun: 'PG options' });

    /* ---------- quick search: a combobox that lives right above each map ---------- */
    const IXD = buildIndex(DEG, d => [d.n, d.full, d.exam, d.elig, d.desc, d.path, d.institutes, d.type], d => [d.n, d.full]);
    const IXM = buildIndex(MAS, x => [x.n, x.full, x.f, x.exam, x.elig, x.paths, x.institutes], x => [x.n, x.full]);
    function quickSearch(cfg) {
      const { root, input, list, clear, ix, items, meta, pick } = cfg;
      let act = -1;
      const opts = () => [...list.querySelectorAll('[role="option"]')];
      const close = () => { list.hidden = true; input.setAttribute('aria-expanded', 'false'); input.removeAttribute('aria-activedescendant'); act = -1; };
      const setAct = i => {
        const o = opts(); if (!o.length) return;
        act = (i + o.length) % o.length;
        o.forEach((el, k) => { el.classList.toggle('act', k === act); el.setAttribute('aria-selected', String(k === act)); });
        input.setAttribute('aria-activedescendant', o[act].id); o[act].scrollIntoView({ block: 'nearest' });
      };
      function render() {
        const q = norm(input.value).slice(0, 70);
        clear.hidden = !input.value;
        if (!q) { list.replaceChildren(); close(); return; }
        const hits = fuzzySearch(ix, q), top = hits.slice(0, 8);
        const lis = top.map((i, k) => {
          const it = items[i];
          const li = E('li', { role: 'option', id: list.id + '-' + k, 'aria-selected': 'false', class: 'qopt' }, E('b', { text: it.n }), E('span', { text: it.full }), E('small', { text: meta(it) }));
          li.addEventListener('mousedown', e => e.preventDefault());   /* keep focus in the input */
          li.addEventListener('click', () => { close(); pick(it, input); });
          return li;
        });
        if (!lis.length) lis.push(E('li', { class: 'qnone', role: 'presentation', text: 'No matches. Try another word or check the spelling.' }));
        if (hits.length > 8) lis.push(E('li', { class: 'qmore', role: 'presentation', text: '+ ' + (hits.length - 8) + ' more. Keep typing to narrow down.' }));
        list.replaceChildren(...lis);
        if (list.hidden && window.innerHeight < 900) root.scrollIntoView({ behavior: REDUCED() ? 'auto' : 'smooth', block: 'start' });   /* keep the results in view on small screens */
        list.hidden = false; input.setAttribute('aria-expanded', 'true'); act = -1;
        say(hits.length + (hits.length === 1 ? ' match' : ' matches'));
      }
      input.addEventListener('input', render);
      input.addEventListener('focus', () => { if (input.value) render(); });
      input.addEventListener('keydown', e => {
        if (e.key === 'ArrowDown') { e.preventDefault(); if (list.hidden) render(); setAct(act + 1); }
        else if (e.key === 'ArrowUp') { e.preventDefault(); setAct(act - 1); }
        else if (e.key === 'Enter') { const o = opts(); const el = o[act >= 0 ? act : 0]; if (el) { e.preventDefault(); el.click(); } }
        else if (e.key === 'Escape' && (input.value || !list.hidden)) { e.stopPropagation(); input.value = ''; render(); }
      });
      clear.addEventListener('click', () => { input.value = ''; render(); input.focus(); });
      document.addEventListener('click', e => { if (!root.contains(e.target)) close(); });
    }
    quickSearch({ root: $('#degreeQuick'), input: $('#degreeSearch'), list: $('#degreeResults'), clear: $('#degreeClear'), ix: IXD, items: DEG, meta: d => years(d.yrs) + ' · ' + d.exam, pick: (d, from) => openView(() => degreeView(d.id), from) });
    quickSearch({ root: $('#masterQuick'), input: $('#masterSearch'), list: $('#masterResults'), clear: $('#masterClear'), ix: IXM, items: MAS, meta: m => m.dur + ' · ' + m.f, pick: (m, from) => openView(() => masterView(m.id), from) });
    $('#degreeSearch').placeholder = 'Search ' + DEG.length + ' degrees, exams or careers (try "btech", "doctor", "NEET")…';
    $('#masterSearch').placeholder = 'Search ' + MAS.length + ' master\'s and PG programmes (try "MBA", "data science")…';

    /* ---------- tabs ---------- */
    const tabs = [$('#tabBachelor'), $('#tabMasters')], panes = [$('#bachelorPane'), $('#mastersPane')];
    function showTab(n) {
      tabs.forEach((t, i) => { t.setAttribute('aria-selected', String(i === n)); t.tabIndex = i === n ? 0 : -1; panes[i].hidden = i !== n; });
      closeDlg(false);
      panes[n].classList.remove('pane-in'); void panes[n].offsetWidth; panes[n].classList.add('pane-in');
      (n === 0 ? flowB : flowM).intro();
      (n === 0 ? flowB : flowM).redraw();
    }
    tabs.forEach((t, i) => {
      t.addEventListener('click', () => { showTab(i); window.scrollTo({ top: 0, behavior: REDUCED() ? 'auto' : 'smooth' }); });
      t.addEventListener('keydown', e => {
        const k = { ArrowRight: i + 1, ArrowLeft: i - 1, Home: 0, End: tabs.length - 1 }[e.key]; if (k == null) return;
        e.preventDefault(); const n = (k + tabs.length) % tabs.length; showTab(n); tabs[n].focus();
      });
    });

    /* ---------- static text driven by data ---------- */
    document.querySelectorAll('[data-count]').forEach(el => { el.textContent = el.getAttribute('data-count') === 'degrees' ? DEG.length : MAS.length; });
    $('#updated').textContent = (UPDATED ? 'Last reviewed ' + UPDATED + '. ' : '') + 'All figures are indicative and sourced from public career compendiums.';
    $('#eligNote').textContent = 'Master\'s programmes commonly take 1–2 years (many Indian ones take 2). ' + ELIG_NOTE;
    document.querySelectorAll('.step').forEach((s, i) => s.style.setProperty('--i', i % 3));
    syncTray(); renderJourney();
    if (SEEN.size) setTimeout(() => toast('Welcome back! You have explored ' + SEEN.size + ' pathways so far.'), 2600);
  }

  setupScrollUi();
  boot();
})();
