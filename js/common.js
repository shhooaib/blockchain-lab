/* BlockLab shared helpers: shell (nav/footer), hashing, chain helpers, storage, toasts */
(function (global) {
  'use strict';

  var MODS = [
    { n: 1, slug: 'm1', name: 'Salary Blockchain', short: 'Salary', tag: 'Payroll ledger', desc: 'A tamper-evident payroll ledger. Add salary records, validate the chain, then tamper with a block and watch validation fail.', stat: 'SHA-256 chain' },
    { n: 2, slug: 'm2', name: 'Password Security Lab', short: 'Passwords', tag: 'Cryptography', desc: 'Six experiments on hashing, salting, verification, algorithm speed and the avalanche effect.', stat: '6 experiments' },
    { n: 3, slug: 'm3', name: 'Ethereum Transaction Simulator', short: 'Ethereum', tag: 'Wallets & gas', desc: 'Wallets, ETH transfers, gas fees, a pending pool and simulated blocks, all with exact integer maths.', stat: 'Wei-exact maths' },
    { n: 4, slug: 'm4', name: 'Consortium Network Simulator', short: 'Consortium', tag: 'Permissioned network', desc: 'A multi-organisation supply-chain network with roles, endorsement policies, peers and a shared ledger.', stat: '4 roles' },
    { n: 5, slug: 'm5', name: 'Blockchain Identity Verification', short: 'Identity', tag: 'Credentials', desc: 'Register identities, issue credentials, grant access and verify claims against hash commitments on a ledger.', stat: '4 roles' }
  ];

  /* ---------- small utilities ---------- */
  function esc(s) {
    return String(s == null ? '' : s).replace(/[&<>"']/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
    });
  }
  function $(sel, root) { return (root || document).querySelector(sel); }
  function $$(sel, root) { return Array.prototype.slice.call((root || document).querySelectorAll(sel)); }
  function short(h, n) { n = n || 10; h = String(h || ''); return h.length > n * 2 + 1 ? h.slice(0, n) + '…' + h.slice(-6) : h; }
  function fmtTime(iso) {
    var d = new Date(iso); if (isNaN(d)) return String(iso);
    return d.toLocaleString(undefined, { day: '2-digit', month: 'short', year: 'numeric', hour: '2-digit', minute: '2-digit', second: '2-digit' });
  }
  function randHex(bytes) {
    var a = new Uint8Array(bytes);
    if (global.crypto && crypto.getRandomValues) crypto.getRandomValues(a);
    else for (var i = 0; i < bytes; i++) a[i] = Math.floor(Math.random() * 256);
    return Array.prototype.map.call(a, function (b) { return b.toString(16).padStart(2, '0'); }).join('');
  }
  function canon(v) { // stable JSON with sorted keys so hashes never depend on key order
    if (v === null || typeof v !== 'object') return JSON.stringify(v);
    if (Array.isArray(v)) return '[' + v.map(canon).join(',') + ']';
    return '{' + Object.keys(v).sort().map(function (k) { return JSON.stringify(k) + ':' + canon(v[k]); }).join(',') + '}';
  }
  function clone(o) { return JSON.parse(JSON.stringify(o)); }

  /* ---------- storage with graceful fallback ---------- */
  var mem = {};
  var store = {
    get: function (k, d) {
      try { var v = localStorage.getItem(k); if (v != null) return JSON.parse(v); } catch (e) { if (k in mem) return clone(mem[k]); }
      return k in mem ? clone(mem[k]) : d;
    },
    set: function (k, v) { mem[k] = clone(v); try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) { /* storage unavailable: memory only */ } },
    del: function (k) { delete mem[k]; try { localStorage.removeItem(k); } catch (e) { } }
  };

  /* ---------- SHA-256 (synchronous, UTF-8) ---------- */
  var K = [], H0 = [];
  (function () {
    var primes = [], n = 2;
    while (primes.length < 64) { var ok = true; for (var i = 0; i < primes.length; i++) if (n % primes[i] === 0) { ok = false; break; } if (ok) primes.push(n); n++; }
    for (var j = 0; j < 64; j++) K.push((Math.pow(primes[j], 1 / 3) % 1) * 4294967296 | 0);
    for (var m = 0; m < 8; m++) H0.push((Math.pow(primes[m], 1 / 2) % 1) * 4294967296 | 0);
  })();
  function utf8(str) { return new TextEncoder().encode(str); }
  function toHex(words) { return words.map(function (w) { return (w >>> 0).toString(16).padStart(8, '0'); }).join(''); }
  function sha256Bytes(bytes) {
    var len = bytes.length, total = ((len + 9 + 63) >> 6) << 6, buf = new Uint8Array(total);
    buf.set(bytes); buf[len] = 0x80;
    var dv = new DataView(buf.buffer);
    dv.setUint32(total - 8, Math.floor(len / 0x20000000), false);
    dv.setUint32(total - 4, (len << 3) >>> 0, false);
    var h = H0.slice(), w = new Int32Array(64);
    for (var off = 0; off < total; off += 64) {
      for (var i = 0; i < 16; i++) w[i] = dv.getInt32(off + i * 4, false);
      for (i = 16; i < 64; i++) {
        var a = w[i - 15], b = w[i - 2];
        var s0 = ((a >>> 7) | (a << 25)) ^ ((a >>> 18) | (a << 14)) ^ (a >>> 3);
        var s1 = ((b >>> 17) | (b << 15)) ^ ((b >>> 19) | (b << 13)) ^ (b >>> 10);
        w[i] = (w[i - 16] + s0 + w[i - 7] + s1) | 0;
      }
      var A = h[0], B = h[1], C = h[2], D = h[3], E = h[4], F = h[5], G = h[6], Hh = h[7];
      for (i = 0; i < 64; i++) {
        var S1 = ((E >>> 6) | (E << 26)) ^ ((E >>> 11) | (E << 21)) ^ ((E >>> 25) | (E << 7));
        var ch = (E & F) ^ (~E & G);
        var t1 = (Hh + S1 + ch + K[i] + w[i]) | 0;
        var S0 = ((A >>> 2) | (A << 30)) ^ ((A >>> 13) | (A << 19)) ^ ((A >>> 22) | (A << 10));
        var mj = (A & B) ^ (A & C) ^ (B & C);
        var t2 = (S0 + mj) | 0;
        Hh = G; G = F; F = E; E = (D + t1) | 0; D = C; C = B; B = A; A = (t1 + t2) | 0;
      }
      h[0] = (h[0] + A) | 0; h[1] = (h[1] + B) | 0; h[2] = (h[2] + C) | 0; h[3] = (h[3] + D) | 0;
      h[4] = (h[4] + E) | 0; h[5] = (h[5] + F) | 0; h[6] = (h[6] + G) | 0; h[7] = (h[7] + Hh) | 0;
    }
    return toHex(h);
  }
  function sha256(str) { return sha256Bytes(utf8(String(str))); }

  /* ---------- generic hash-linked chain helpers ---------- */
  var ZERO = new Array(65).join('0');
  function hashBlock(b) { return sha256(canon({ i: b.index, t: b.timestamp, p: b.prevHash, d: b.data })); }
  function makeBlock(index, data, prevHash, ts) {
    var b = { index: index, timestamp: ts || new Date().toISOString(), data: data, prevHash: prevHash };
    b.hash = hashBlock(b); return b;
  }
  /* Checks every block, genesis included. Returns {ok, issues:[{index, reason}]} */
  function verifyChain(blocks) {
    var issues = [];
    blocks.forEach(function (b, i) {
      if (b.index !== i) issues.push({ index: i, reason: 'Block index is ' + b.index + ' but its position is ' + i });
      if (hashBlock(b) !== b.hash) issues.push({ index: i, reason: 'Contents no longer match the stored hash' });
      var expect = i === 0 ? ZERO : blocks[i - 1].hash;
      if (b.prevHash !== expect) issues.push({ index: i, reason: i === 0 ? 'Genesis block must point to the all-zero hash' : 'Previous-hash link does not match block ' + (i - 1) });
    });
    return { ok: issues.length === 0, issues: issues };
  }

  /* ---------- UI helpers ---------- */
  function toast(msg, kind) {
    var root = document.getElementById('toast-root');
    if (!root) { root = document.createElement('div'); root.id = 'toast-root'; root.setAttribute('role', 'status'); root.setAttribute('aria-live', 'polite'); document.body.appendChild(root); }
    var t = document.createElement('div'); t.className = 'toast ' + (kind || ''); t.textContent = msg; root.appendChild(t);
    setTimeout(function () { t.style.opacity = '0'; t.style.transition = 'opacity .3s'; setTimeout(function () { t.remove(); }, 320); }, 3200);
  }
  function copy(text) {
    function fallback() {
      var ta = document.createElement('textarea'); ta.value = text; ta.style.position = 'fixed'; ta.style.opacity = '0';
      document.body.appendChild(ta); ta.select();
      try { document.execCommand('copy'); toast('Copied to clipboard', 'ok'); } catch (e) { toast('Select the text and copy it manually', 'bad'); }
      ta.remove();
    }
    if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(text).then(function () { toast('Copied to clipboard', 'ok'); }, fallback);
    else fallback();
  }
  function on(root, evt, sel, fn) {
    root.addEventListener(evt, function (e) {
      var t = e.target.closest ? e.target.closest(sel) : null;
      if (t && root.contains(t)) fn(e, t);
    });
  }

  /* ---------- shell: shared nav + footer ---------- */
  function shell(opts) {
    opts = opts || {};
    var mod = opts.mod || 0, base = document.body.getAttribute('data-base') || '';
    var links = '<a href="' + base + 'index.html"' + (mod === 0 ? ' class="on"' : '') + '>Hub</a>' +
      MODS.map(function (m) {
        return '<a href="' + base + m.slug + '/index.html"' + (m.n === mod ? ' class="on"' : '') + '>' + String(m.n).padStart(2, '0') + ' ' + esc(m.short) + '</a>';
      }).join('');
    var nav = document.getElementById('nav');
    if (nav) nav.outerHTML =
      '<a class="skip" href="#main">Skip to content</a>' +
      '<header class="nav"><div class="nav-in">' +
      '<a class="logo" href="' + base + 'index.html"><span class="logo-mark">BL</span>BlockLab<span class="pulse" aria-hidden="true"></span></a>' +
      '<nav class="nav-links" id="navlinks" aria-label="Modules">' + links + '</nav>' +
      '<a class="pill-cta desk" href="' + base + 'index.html#modules">All modules</a>' +
      '<button class="nav-toggle" id="navtoggle" aria-expanded="false" aria-controls="navlinks" type="button">Menu</button>' +
      '</div></header>';
    var tg = document.getElementById('navtoggle');
    if (tg) tg.addEventListener('click', function () {
      var l = document.getElementById('navlinks'), open = l.classList.toggle('open');
      tg.setAttribute('aria-expanded', open ? 'true' : 'false');
    });
    var foot = document.getElementById('foot');
    if (foot) {
      var next = MODS[mod % 5];
      var nextBlock = mod === 0 ? '' :
        '<section class="foot-next"><div class="wrap"><p class="kicker">Up next · Module ' + String(next.n).padStart(2, '0') + '</p>' +
        '<h2>' + esc(next.name) + '</h2><p style="max-width:52ch;margin-top:1rem">' + esc(next.desc) + '</p>' +
        '<div class="foot-links"><a class="btn lg" href="' + base + next.slug + '/index.html">Open module <span class="arrow">→</span></a>' +
        '<a class="btn ghost lg" href="' + base + 'index.html#modules">Back to all modules</a></div></div></section>';
      foot.outerHTML = nextBlock +
        '<footer class="foot-base"><div class="wrap"><span>BlockLab · Blockchain technology project activity</span>' +
        '<span>Educational simulations · Use fictional data only · Everything runs in your browser</span></div></footer>';
    }
  }

  global.BL = {
    MODS: MODS, esc: esc, $: $, $$: $$, short: short, fmtTime: fmtTime, randHex: randHex, canon: canon, clone: clone,
    store: store, sha256: sha256, sha256Bytes: sha256Bytes, utf8: utf8, ZERO: ZERO, hashBlock: hashBlock,
    makeBlock: makeBlock, verifyChain: verifyChain, toast: toast, copy: copy, on: on, shell: shell
  };
})(window);
