// The page of Exit Proof. The answers come from web/worker.js, which runs the Python scanner of this repository
// in the browser. The numbers come from the evidence files of the repository, read when the page loads.

const $ = (id) => document.getElementById(id);
const ROOT = new URL('..', import.meta.url).href;
const LABEL = { 2: 'PROVEN EXIT', 1: 'EXIT WINDOW', 0: 'KEYHOLDER TRUST', U: 'UNPROVEN' };
// Where a line of evidence comes from (the tags of tools/exitproof.py)
const TAGS = {
  chain: 'read from current chain state',
  code: 'read from the deployed wasm',
  view: 'returned by a view method of the contract: self-reported',
  hist: 'the deployment history, as an indexer lists it',
  proof: 'a machine-checked theorem registered for this exact code hash',
  name: 'inferred from an exported method name: the weakest evidence',
};

// ---- the network switch: two buttons in place of a drop-down; the hidden #network holds the value -----------
function setNet(net) {
  $('network').value = net;
  for (const b of document.querySelectorAll('.seg [data-net]')) b.setAttribute('aria-checked', String(b.dataset.net === net));
}
for (const b of document.querySelectorAll('.seg [data-net]')) b.addEventListener('click', () => setNet(b.dataset.net));

// ---- the worker -------------------------------------------------------------------------------------------
let worker = null;
let seq = 0;
const waiting = new Map();
const listeners = new Set(); // functions that show the worker's progress lines

function startWorker() {
  if (worker) return;
  worker = new Worker(new URL('worker.js', import.meta.url));
  worker.onmessage = (e) => {
    const m = e.data;
    if (m.progress) listeners.forEach((f) => f(m.progress));
    else if (m.failed) {
      listeners.forEach((f) => f(m.failed));
      waiting.forEach((done) => done({ status: 'error', error: m.failed }));
      waiting.clear();
    } else if (m.id !== undefined) {
      const done = waiting.get(m.id);
      waiting.delete(m.id);
      if (done) done(m.answer);
    }
  };
  worker.onerror = (e) => {
    const text = `The scanner stopped: ${e.message || 'the worker could not be loaded'}`;
    waiting.forEach((done) => done({ status: 'error', error: text }));
    waiting.clear();
  };
}

function ask(kind, account, network, detail) {
  startWorker();
  return new Promise((done) => {
    const id = ++seq;
    waiting.set(id, done);
    worker.postMessage({ id, kind, account, network, detail });
  });
}

// What a status other than "ok" means, in words. An unread chain is said as such and is never a stage.
function trouble(a) {
  if (a.status === 'not_found')
    return `No answer: ${a.error.replace(/try --network (\w+)/, 'choose $1 in the list')}.`;
  if (a.status === 'bad_argument') return `No answer: ${a.error}.`;
  if (a.status === 'unreadable')
    return `The chain could not be read (${a.error}). There is no verdict: ask again in a minute.`;
  return `The scanner failed: ${a.error}`;
}

// ---- the exit stage ---------------------------------------------------------------------------------------
let asked = 0;

async function readStage(detail) {
  const account = $('account').value.trim().toLowerCase();
  const network = $('network').value;
  const mine = ++asked;
  const t0 = performance.now();
  const status = $('exit-status');
  const show = (text) => mine === asked && (status.textContent = text);
  listeners.add(show);
  $('check-exit').disabled = true;
  $('full').disabled = true;
  $('exit-result').hidden = detail !== 'full';
  show(
    detail === 'full'
      ? `Reading who holds each power on ${account}: up to 100 reads…`
      : `Reading ${account} on ${network}…`,
  );
  const a = await ask('exit', account, network, detail);
  listeners.delete(show);
  if (mine !== asked) return;
  $('check-exit').disabled = false;
  $('full').disabled = false;
  if (a.status !== 'ok') {
    $('exit-result').hidden = true;
    status.textContent = trouble(a);
    return;
  }
  const st = a.view.stage;
  const head = $('decision');
  head.className = `stage-line s${st.level}`;
  head.textContent = '';
  const badge = document.createElement('span');
  badge.className = 'lvl';
  badge.textContent = st.level;
  head.append(badge, ` ${st.label}${st.condition ? ', under a stated condition' : ''}`);
  if (st.level === '1' && st.delay_seconds) {
    const s = st.delay_seconds;
    head.append(` · ${s >= 3600 ? `${Math.floor(s / 3600)} h` : `${Math.max(1, Math.floor(s / 60))} min`}`);
  }
  const why = $('why');
  why.textContent = '';
  for (const line of st.why || []) {
    const li = document.createElement('li');
    const m = line.match(/^(.*?)\s*\[(chain|code|view|hist|proof|name)\]$/);
    li.textContent = m ? m[1] : line;
    if (m) {
      const tag = document.createElement('span');
      tag.className = `tag t-${m[2]}`;
      tag.textContent = m[2];
      tag.title = TAGS[m[2]];
      li.append(' ', tag);
    }
    why.append(li);
  }
  $('condition').hidden = !st.condition;
  $('condition').textContent = st.condition ? `Condition: ${st.condition}` : '';
  $('report').textContent = a.report;
  $('full').hidden = detail === 'full';
  $('exit-result').hidden = false;
  const link = `#check=${encodeURIComponent(account)}${network === 'testnet' ? '&net=testnet' : ''}`;
  history.replaceState(null, '', link);
  $('share').hidden = false;
  const secs = ((performance.now() - t0) / 1000).toFixed(1);
  status.textContent =
    detail === 'full'
      ? `${account} on ${network}: the whole report, read in ${secs} s.`
      : `${account} on ${network}: the stage and its reasons, read in ${secs} s. Who holds each power was not read.`;
}

$('share').addEventListener('click', async () => {
  try {
    await navigator.clipboard.writeText(location.href);
    $('share').textContent = 'Link copied';
  } catch {
    $('share').textContent = 'Copy the address bar';
  }
  setTimeout(() => ($('share').textContent = 'Copy a link to this answer'), 2500);
});

// A link of the form #check=<account>[&net=testnet] asks at once.
function fromLink() {
  const q = new URLSearchParams(location.hash.slice(1));
  const acc = q.get('check');
  if (!acc) return;
  $('account').value = acc;
  setNet(q.get('net') === 'testnet' ? 'testnet' : 'mainnet');
  const card = document.getElementById('try');
  if (card.getBoundingClientRect().top > innerHeight * 0.5) card.scrollIntoView({ block: 'start' });
  readStage('stage');
}

// The scanner is about 10 MB of Python: start loading it when a visitor comes near a form, not on the first question.
for (const id of ['try', 'tokens']) {
  const el = document.getElementById(id);
  for (const ev of ['pointerenter', 'focusin', 'touchstart']) el.addEventListener(ev, startWorker, { once: true, passive: true });
}

$('exit-form').addEventListener('submit', (e) => {
  e.preventDefault();
  readStage('stage');
});
$('full').addEventListener('click', () => readStage('full'));
for (const b of document.querySelectorAll('#exit-form .presets button')) {
  b.addEventListener('click', () => {
    $('account').value = b.dataset.account;
    setNet(b.dataset.network);
    readStage('stage');
  });
}

// ---- the token check --------------------------------------------------------------------------------------
let askedToken = 0;

async function checkToken() {
  const token = $('token').value.trim().toLowerCase();
  const mine = ++askedToken;
  const status = $('token-status');
  const show = (text) => mine === askedToken && (status.textContent = text);
  listeners.add(show);
  $('check-token').disabled = true;
  $('token-result').hidden = true;
  show(`Reading ${token} on mainnet…`);
  const a = await ask('token', token, 'mainnet', '');
  listeners.delete(show);
  if (mine !== askedToken) return;
  $('check-token').disabled = false;
  if (a.status !== 'ok') {
    status.textContent = trouble(a);
    return;
  }
  const lines = a.report.split('\n');
  const head = lines.find((l) => l.startsWith('TOKEN CHECK:')) || lines[0];
  const now = a.view.behaves_as_standard_now;
  $('token-decision').className = `stage-line ${now === true ? 's2' : now === false ? 's0' : 'sU'}`;
  $('token-decision').textContent = head.replace('TOKEN CHECK: ', '').split(' — ')[0];
  $('token-report').textContent = a.report;
  $('token-result').hidden = false;
  status.textContent =
    now === true
      ? 'Behaves as the standard now.'
      : now === false
        ? 'Does not behave as the standard now.'
        : 'Whether it behaves as the standard now is not known; the report says why.';
}

$('token-form').addEventListener('submit', (e) => {
  e.preventDefault();
  checkToken();
});
for (const b of document.querySelectorAll('#token-form .presets button')) {
  b.addEventListener('click', () => {
    $('token').value = b.dataset.token;
    checkToken();
  });
}

// ---- the numbers, from the evidence files ----------------------------------------------------------------
const get = (path) => fetch(ROOT + path).then((r) => (r.ok ? r.json() : Promise.reject(new Error(path))));
const n = (x) => x.toLocaleString('en-US').replace(/,/g, ' ');

async function numbers() {
  const [stake, census, pools, conf, mutants] = await Promise.all([
    get('evidence/stake-by-stage.json'),
    get('evidence/contracts-census.json'),
    get('evidence/pools-live.json'),
    get('intents-proof/evidence/conformance.json'),
    get('intents-proof/evidence/model_mutants.json'),
  ]);
  const share = stake.share_by_stage;
  const level = (r) => String(r.stage && r.stage.level !== undefined ? r.stage.level : r.stage);
  const by = { 2: 0, 1: 0, 0: 0, U: 0 };
  for (const r of census) by[level(r)] += 1;
  const receipts = Object.values(conf.replay).reduce((s, r) => s + r.contract_steps, 0);
  const disagree = Object.values(conf.replay).reduce((s, r) => s + r.disagree, 0);
  const changes = mutants.filter((m) => m.result !== 'PASS');
  const noticed = changes.filter((m) => m.result === 'DETECTED').length;

  $('f-share').textContent = `${share['2']}%`;
  $('f-pools').textContent = n(pools.summary.pools_checked);
  $('f-zero').textContent = String(by[0]);
  $('f-zero-label').textContent = `of ${census.length} large contracts are at stage 0`;
  $('f-receipts').textContent = n(receipts);
  $('f-receipts').classList.toggle('long', n(receipts).length > 5);
  if (disagree !== 0) $('f-receipts').nextElementSibling.textContent = `receipts replayed, ${disagree} disagree`;
  $('f-mutants').textContent = String(noticed);
  $('f-mutants-label').textContent = `of ${changes.length} one-line changes of the model noticed`;

  const bar = $('stake-bar');
  for (const lv of ['2', '1', '0', 'U']) {
    const pct = share[lv] || 0;
    if (!pct) continue;
    const part = document.createElement('div');
    part.className = `l${lv.toLowerCase()}`;
    part.style.flexGrow = pct;
    part.textContent = pct >= 20 ? `Stage ${lv} · ${LABEL[lv].toLowerCase()} · ${pct}%` : `${lv} · ${pct}%`;
    bar.append(part);
  }
  const top = stake.by_code.find((c) => c.stage === '2');
  const fak = stake.by_code.reduce((s, c) => s + (c.pools_with_full_access_key || 0), 0);
  $('stake-note').textContent =
    `${share['2']}% is one pool code with no access keys and no upgrade method, run by ${top.pools} validators. ` +
    `The rest is pool code with an upgrade method that takes effect with no delay` +
    (fak ? `, plus ${fak} pool${fak > 1 ? 's' : ''} with a full-access key. ` : '. ') +
    `Snapshot of ${stake.snapshot.slice(0, 10)}: ${n(stake.total_stake_NEAR)} NEAR staked with the validators of one epoch.`;

  const cells = $('cells');
  for (const lv of ['2', '1', '0', 'U']) {
    for (let k = 0; k < by[lv]; k++) {
      const c = document.createElement('i');
      c.className = `l${lv.toLowerCase()}`;
      cells.append(c);
    }
  }
  $('cells-title').textContent = `${census.length} large contracts: bridges, tokens, DeFi`;
  $('cells-note').textContent =
    `${by[2]} at stage 2, ${by[1]} at stage 1, ${by[0]} at stage 0, ${by.U} unproven. ` +
    `At stage 0 the code can change with no delay.`;
}

numbers().catch(() => {
  $('stake-note').textContent =
    'The evidence files could not be read from here. The numbers are in README.md of the repository.';
});

fromLink();
window.addEventListener('hashchange', fromLink);
