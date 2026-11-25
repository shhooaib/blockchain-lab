/* Module 02 — Password Security Lab: all experiment logic */
(function () {
  'use strict';
  var $ = BL.$, esc = BL.esc;

  /* ================= hashing primitives ================= */
  function hex(buf) { return Array.prototype.map.call(new Uint8Array(buf), function (b) { return b.toString(16).padStart(2, '0'); }).join(''); }
  var subtleOK = !!(window.crypto && crypto.subtle);
  function digest(alg, text) {
    if (alg === 'SHA-256' && !subtleOK) return Promise.resolve(BL.sha256(text));
    if (!subtleOK) return Promise.reject(new Error('Web Crypto is unavailable here. Open this page from https:// or http://localhost, or in a current desktop browser.'));
    return crypto.subtle.digest(alg, BL.utf8(text)).then(hex);
  }

  /* SHA3-256 (Keccak-f[1600], BigInt lanes). Verified against NIST test vectors. */
  var M64 = (1n << 64n) - 1n;
  var RC = [0x0000000000000001n, 0x0000000000008082n, 0x800000000000808an, 0x8000000080008000n, 0x000000000000808bn, 0x0000000080000001n, 0x8000000080008081n, 0x8000000000008009n, 0x000000000000008an, 0x0000000000000088n, 0x0000000080008009n, 0x000000008000000an, 0x000000008000808bn, 0x800000000000008bn, 0x8000000000008089n, 0x8000000000008003n, 0x8000000000008002n, 0x8000000000000080n, 0x000000000000800an, 0x800000008000000an, 0x8000000080008081n, 0x8000000000008080n, 0x0000000080000001n, 0x8000000080008008n];
  var ROT = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]; // [x][y]
  function rotl(v, n) { n = BigInt(n); return n === 0n ? v : ((v << n) | (v >> (64n - n))) & M64; }
  function keccakF(A) { // A[x][y]
    for (var r = 0; r < 24; r++) {
      var C = [], D = [], x, y, B = [[], [], [], [], []];
      for (x = 0; x < 5; x++) C[x] = A[x][0] ^ A[x][1] ^ A[x][2] ^ A[x][3] ^ A[x][4];
      for (x = 0; x < 5; x++) D[x] = C[(x + 4) % 5] ^ rotl(C[(x + 1) % 5], 1);
      for (x = 0; x < 5; x++) for (y = 0; y < 5; y++) A[x][y] ^= D[x];
      for (x = 0; x < 5; x++) for (y = 0; y < 5; y++) B[y][(2 * x + 3 * y) % 5] = rotl(A[x][y], ROT[x][y]);
      for (x = 0; x < 5; x++) for (y = 0; y < 5; y++) A[x][y] = B[x][y] ^ ((~B[(x + 1) % 5][y] & M64) & B[(x + 2) % 5][y]);
      A[0][0] ^= RC[r];
    }
  }
  function sha3_256(text) {
    var bytes = BL.utf8(text), rate = 136, padLen = rate - (bytes.length % rate);
    var msg = new Uint8Array(bytes.length + padLen); msg.set(bytes);
    msg[bytes.length] ^= 0x06; msg[msg.length - 1] ^= 0x80;
    var A = [[0n, 0n, 0n, 0n, 0n], [0n, 0n, 0n, 0n, 0n], [0n, 0n, 0n, 0n, 0n], [0n, 0n, 0n, 0n, 0n], [0n, 0n, 0n, 0n, 0n]];
    for (var off = 0; off < msg.length; off += rate) {
      for (var i = 0; i < rate / 8; i++) {
        var lane = 0n; for (var b = 7; b >= 0; b--) lane = (lane << 8n) | BigInt(msg[off + i * 8 + b]);
        A[i % 5][Math.floor(i / 5)] ^= lane;
      }
      keccakF(A);
    }
    var out = '';
    for (var j = 0; j < 4; j++) { var l = A[j % 5][Math.floor(j / 5)]; for (var k = 0; k < 8; k++) { out += Number((l >> BigInt(8 * k)) & 0xffn).toString(16).padStart(2, '0'); } }
    return out;
  }
  window.BLsha3 = sha3_256;

  /* ================= password hashing: bcrypt with PBKDF2 fallback ================= */
  function bc() { return (window.dcodeIO && window.dcodeIO.bcrypt) || window.bcrypt || null; }
  var Pwd = {
    engine: function () { return bc() ? 'bcrypt' : 'pbkdf2'; },
    label: function () { return bc() ? 'bcrypt (bcryptjs)' : 'PBKDF2-SHA256 (bcrypt library not loaded)'; },
    tooLong: function (pw) { return bc() && BL.utf8(pw).length > 72; },
    hash: function (pw, cost) {
      var b = bc();
      if (b) return new Promise(function (res, rej) { b.hash(pw, cost, function (e, h) { e ? rej(e) : res(h); }); });
      var salt = new Uint8Array(16); crypto.getRandomValues(salt);
      var iter = Math.pow(2, cost + 6);
      return pbkdf2(pw, salt, iter).then(function (h) { return '$pbkdf2-sha256$i=' + iter + '$' + hex(salt) + '$' + hex(h); });
    },
    verify: function (pw, stored) {
      var b = bc();
      if (stored.indexOf('$pbkdf2-sha256$') === 0) {
        var p = stored.split('$'), iter = parseInt(p[2].slice(2), 10), salt = new Uint8Array(p[3].match(/../g).map(function (h) { return parseInt(h, 16); }));
        return pbkdf2(pw, salt, iter).then(function (h) { return hex(h) === p[4]; });
      }
      if (!b) return Promise.resolve(false);
      return new Promise(function (res, rej) { b.compare(pw, stored, function (e, ok) { e ? rej(e) : res(ok); }); });
    }
  };
  function pbkdf2(pw, salt, iter) {
    return crypto.subtle.importKey('raw', BL.utf8(pw), 'PBKDF2', false, ['deriveBits'])
      .then(function (k) { return crypto.subtle.deriveBits({ name: 'PBKDF2', hash: 'SHA-256', salt: salt, iterations: iter }, k, 256); });
  }

  function human(sec) {
    if (!isFinite(sec)) return 'effectively never';
    if (sec < 1) return 'under a second';
    var u = [['year', 31557600], ['day', 86400], ['hour', 3600], ['minute', 60], ['second', 1]];
    if (sec >= 31557600 * 1e9) return 'longer than the age of the universe';
    for (var i = 0; i < u.length; i++) if (sec >= u[i][1]) { var v = sec / u[i][1]; return (v >= 100 ? Math.round(v).toLocaleString() : v.toFixed(v < 10 ? 1 : 0)) + ' ' + u[i][0] + (Math.round(v) === 1 ? '' : 's'); }
    return Math.round(sec) + ' seconds';
  }
  function busy(btn, on, label) { if (!btn) return; btn.disabled = on; if (on) { btn.dataset.l = btn.textContent; btn.textContent = label || 'Working…'; } else if (btn.dataset.l) btn.textContent = btn.dataset.l; }
  function copyBtn(t) { return '<button class="btn ghost sm" type="button" data-copy="' + esc(t) + '">Copy</button>'; }

  document.addEventListener('click', function (e) {
    var c = e.target.closest && e.target.closest('[data-copy]'); if (c) BL.copy(c.getAttribute('data-copy'));
  });

  var page = document.body.getAttribute('data-page');

  /* ================= 01 hashing ================= */
  function initHashing() {
    $('#hashForm').addEventListener('submit', function (e) {
      e.preventDefault();
      var v = $('#hashInput').value, out = $('#hashResults');
      if (!v) { out.innerHTML = '<div class="notice warn">Type some sample text first.</div>'; return; }
      var algs = [['SHA-1', 'SHA-1', 160, 'Obsolete: collisions have been demonstrated. Shown for comparison only.'], ['SHA-256', 'SHA-256', 256, 'The workhorse of SHA-2. Used in many protocols, Bitcoin included.'], ['SHA-512', 'SHA-512', 512, 'Longer SHA-2 variant with a 512-bit digest.']];
      busy($('#hashBtn'), true);
      Promise.all(algs.map(function (a) { return digest(a[1], v); })).then(function (hs) {
        out.innerHTML = '<p class="hint" style="margin:1rem 0 .75rem">Input: ' + BL.utf8(v).length + ' bytes (UTF-8)</p><div class="grid g3">' + algs.map(function (a, i) {
          return '<div class="card white sm"><div class="row between"><h4>' + a[0] + '</h4><span class="badge' + (a[0] === 'SHA-1' ? ' warn' : '') + '">' + a[2] + ' bits · ' + hs[i].length + ' hex</span></div><span class="hash" style="margin:.7rem 0">' + hs[i] + '</span><p class="hint">' + a[3] + '</p>' + copyBtn(hs[i]) + '</div>';
        }).join('') + '</div>';
      }).catch(function (err) { out.innerHTML = '<div class="notice bad">' + esc(err.message) + '</div>'; }).then(function () { busy($('#hashBtn'), false); });
    });
  }

  /* ================= 02 salt ================= */
  function initSalt() {
    $('#saltForm').addEventListener('submit', function (e) {
      e.preventDefault();
      var pw = $('#saltInput').value, out = $('#saltResults');
      if (!pw) { out.innerHTML = '<div class="notice warn">Type a sample password first.</div>'; return; }
      var s1 = BL.randHex(16), s2 = BL.randHex(16);
      busy($('#saltBtn'), true);
      Promise.all([digest('SHA-256', pw), digest('SHA-256', s1 + pw), digest('SHA-256', s2 + pw)]).then(function (r) {
        var plain = r[0], h1 = r[1], h2 = r[2];
        out.innerHTML =
          '<div class="grid g2" style="margin-top:1.25rem"><div class="card white sm"><div class="row between"><h4>Without salt</h4><span class="badge bad">Identical</span></div>' +
          '<p class="hint">Alice and Bob chose the same password, so the database stores the same value twice. Anyone reading it can see they match.</p>' +
          '<label>Alice · SHA-256(password)</label><span class="hash">' + plain + '</span><label style="margin-top:.8rem">Bob · SHA-256(password)</label><span class="hash">' + plain + '</span></div>' +
          '<div class="card white sm"><div class="row between"><h4>With a unique salt</h4><span class="badge ok">' + (h1 !== h2 ? 'Different' : 'Collision?!') + '</span></div>' +
          '<p class="hint">Same password, two random 128-bit salts. Stored values look unrelated, and a precomputed table cannot cover them.</p>' +
          '<label>Alice · salt</label><span class="hash">' + s1 + '</span><label style="margin-top:.5rem">Alice · SHA-256(salt + password)</label><span class="hash">' + h1 + '</span>' +
          '<label style="margin-top:.8rem">Bob · salt</label><span class="hash">' + s2 + '</span><label style="margin-top:.5rem">Bob · SHA-256(salt + password)</label><span class="hash">' + h2 + '</span></div></div>' +
          '<div class="notice" style="margin-top:1rem">A salt defeats shared lookup tables, but plain SHA-256 is still fast to guess. Real systems combine a salt with a slow function (see experiment 03 and 04).</div>';
      }).catch(function (err) { out.innerHTML = '<div class="notice bad">' + esc(err.message) + '</div>'; }).then(function () { busy($('#saltBtn'), false); });
    });
  }

  /* ================= 03 verification ================= */
  var accounts = [], fails = {};
  var MAX_FAILS = 5, LOCK_MS = 30000;
  function renderAccounts() {
    var box = $('#accountList');
    if (!accounts.length) { box.innerHTML = '<div class="empty">No demo accounts yet. Create one above.</div>'; return; }
    box.innerHTML = '<div class="tw"><table><thead><tr><th>Username</th><th>Stored string</th><th>Parts</th><th></th></tr></thead><tbody>' + accounts.map(function (a, i) {
      var parts;
      if (a.hash.indexOf('$pbkdf2') === 0) { var p = a.hash.split('$'); parts = 'PBKDF2-SHA256 · ' + p[2].slice(2) + ' iterations · salt ' + BL.short(p[3], 6); }
      else { var q = a.hash.split('$'); parts = 'bcrypt ' + q[1] + ' · cost ' + q[2] + ' · salt ' + q[3].slice(0, 22); }
      return '<tr><td><b>' + esc(a.user) + '</b></td><td><span class="hash">' + esc(a.hash) + '</span></td><td class="hint">' + esc(parts) + '</td><td><button class="btn ghost sm" data-del="' + i + '" type="button">Delete</button></td></tr>';
    }).join('') + '</tbody></table></div>';
  }
  function msg(el, kind, text) { el.className = 'notice ' + kind; el.style.marginTop = '1rem'; el.textContent = text; }
  function initVerification() {
    $('#engineNote').textContent = 'Engine in use: ' + Pwd.label() + '.';
    $('#registerForm').addEventListener('submit', function (e) {
      e.preventDefault();
      var u = $('#regUser').value.trim().toLowerCase(), p = $('#regPass').value, m = $('#registerMsg');
      if (!/^[a-z0-9_.-]{3,24}$/.test(u)) return msg(m, 'bad', 'Username must be 3–24 characters: letters, digits, dot, dash or underscore.');
      if (accounts.some(function (a) { return a.user === u; })) return msg(m, 'bad', 'That username already exists.');
      if (p.length < 8) return msg(m, 'bad', 'Use at least 8 characters.');
      if (Pwd.tooLong(p)) return msg(m, 'bad', 'bcrypt only reads the first 72 bytes, so longer passwords are refused instead of being silently cut.');
      busy($('#registerBtn'), true, 'Hashing…');
      var t0 = performance.now();
      Pwd.hash(p, 10).then(function (h) {
        accounts.push({ user: u, hash: h }); $('#regPass').value = ''; renderAccounts();
        msg(m, 'ok', 'Account “' + u + '” created in ' + Math.round(performance.now() - t0) + ' ms. The password was discarded; only the string below is stored.');
      }).catch(function (err) { msg(m, 'bad', err.message); }).then(function () { busy($('#registerBtn'), false); });
    });
    $('#loginForm').addEventListener('submit', function (e) {
      e.preventDefault();
      var u = $('#loginUser').value.trim().toLowerCase(), p = $('#loginPass').value, m = $('#loginMsg');
      if (!u || !p) return msg(m, 'warn', 'Enter both a username and a password.');
      var f = fails[u] || (fails[u] = { n: 0, until: 0 });
      if (Date.now() < f.until) return msg(m, 'bad', 'Too many failed attempts. Try again in ' + Math.ceil((f.until - Date.now()) / 1000) + ' seconds. Rate limiting is a real defence against online guessing.');
      var acc = accounts.filter(function (a) { return a.user === u; })[0];
      busy($('#loginBtn'), true, 'Checking…');
      var t0 = performance.now();
      // Unknown users still pay for one hash so response time does not reveal which usernames exist.
      var job = acc ? Pwd.verify(p, acc.hash) : Pwd.hash(p, 10).then(function () { return false; });
      job.then(function (ok) {
        var ms = Math.round(performance.now() - t0);
        if (ok) { f.n = 0; msg(m, 'ok', 'Credentials verified in ' + ms + ' ms. The candidate was hashed with the stored salt and cost, and the result matched.'); }
        else {
          f.n++; if (f.n >= MAX_FAILS) { f.until = Date.now() + LOCK_MS; f.n = 0; }
          msg(m, 'bad', 'Invalid username or password (' + ms + ' ms). The message is the same whether the username exists or not.');
        }
      }).catch(function (err) { msg(m, 'bad', err.message); }).then(function () { busy($('#loginBtn'), false); });
    });
    $('#accountList').addEventListener('click', function (e) { var d = e.target.closest('[data-del]'); if (d) { accounts.splice(+d.dataset.del, 1); renderAccounts(); } });
    renderAccounts();
  }

  /* ================= 04 comparison ================= */
  function initComparison() {
    $('#engineNote').textContent = 'Slow-hash engine: ' + Pwd.label() + '.';
    $('#compareForm').addEventListener('submit', function (e) {
      e.preventDefault();
      var input = $('#compareInput').value || 'sample', cost = parseInt($('#bcryptCost').value, 10), out = $('#compareResults'), btn = $('#compareBtn');
      busy(btn, true, 'Measuring…');
      out.innerHTML = '<div class="empty">Running timings. The slow hash needs a few seconds.</div>';
      var rows = [];
      function timeAsync(name, kind, n, fn) {
        return fn().then(function () { // warm-up
          var t0 = performance.now(), p = Promise.resolve();
          for (var i = 0; i < n; i++) p = p.then(fn);
          return p.then(function () { rows.push({ name: name, kind: kind, ms: (performance.now() - t0) / n, n: n }); });
        });
      }
      function timeSync(name, kind, n, fn) {
        fn(); var t0 = performance.now(); for (var i = 0; i < n; i++) fn();
        rows.push({ name: name, kind: kind, ms: (performance.now() - t0) / n, n: n });
      }
      var chain = Promise.resolve();
      [['SHA-1', 'SHA-1'], ['SHA-256', 'SHA-256'], ['SHA-512', 'SHA-512']].forEach(function (a) {
        chain = chain.then(function () { return timeAsync(a[0], 'General-purpose', 300, function () { return digest(a[1], input); }); });
      });
      chain = chain.then(function () { timeSync('SHA3-256', 'General-purpose', 60, function () { return sha3_256(input); }); });
      chain = chain.then(function () { return timeAsync(Pwd.engine() === 'bcrypt' ? 'bcrypt (cost ' + cost + ')' : 'PBKDF2-SHA256 (cost ' + cost + ')', 'Password hash', cost >= 11 ? 2 : 4, function () { return Pwd.hash(input, cost); }); });
      chain.then(function () {
        var maxRate = Math.max.apply(null, rows.map(function (r) { return 1000 / r.ms; })), top = Math.log10(maxRate) + 0.3;
        out.innerHTML = '<div class="tw" style="margin-top:1.25rem"><table><thead><tr><th>Algorithm</th><th>Type</th><th class="right">Avg time</th><th class="right">Hashes / second</th><th style="min-width:180px">Relative speed (log scale)</th><th class="right">1 billion guesses</th></tr></thead><tbody>' + rows.map(function (r) {
          var rate = 1000 / r.ms, w = Math.max(3, 100 * Math.log10(Math.max(rate, 1)) / top);
          return '<tr><td><b>' + esc(r.name) + '</b></td><td><span class="badge' + (r.kind === 'Password hash' ? ' ok' : '') + '">' + r.kind + '</span></td><td class="right num">' + (r.ms < 1 ? (r.ms * 1000).toFixed(1) + ' µs' : r.ms.toFixed(1) + ' ms') + '</td><td class="right num">' + Math.round(rate).toLocaleString() + '</td><td><div class="bar"><i style="width:' + w.toFixed(1) + '%"></i></div></td><td class="right num">' + human(1e9 / rate) + '</td></tr>';
        }).join('') + '</tbody></table></div><p class="hint">Single-thread timings in this tab, including promise overhead for the Web Crypto rows. Attackers use GPUs and many cores, so real guessing rates against fast hashes are far higher. The ratio is the lesson.</p>';
      }).catch(function (err) { out.innerHTML = '<div class="notice bad">' + esc(err.message) + '</div>'; }).then(function () { busy(btn, false); });
    });
  }

  /* ================= 05 avalanche ================= */
  function popcount(n) { n = n - ((n >> 1) & 0x55555555); n = (n & 0x33333333) + ((n >> 2) & 0x33333333); return (((n + (n >> 4)) & 0x0f0f0f0f) * 0x01010101) >> 24; }
  function initAvalanche() {
    $('#avalancheForm').addEventListener('submit', function (e) {
      e.preventDefault();
      var a = $('#avOriginal').value, b = $('#avModified').value, out = $('#avResults');
      Promise.all([digest('SHA-256', a), digest('SHA-256', b)]).then(function (h) {
        var ha = h[0], hb = h[1], flips = 0, cells = '', hl = '';
        for (var i = 0; i < 64; i++) {
          var x = parseInt(ha[i], 16) ^ parseInt(hb[i], 16); flips += popcount(x);
          hl += x ? '<span class="diff">' + hb[i] + '</span>' : hb[i];
          for (var bit = 3; bit >= 0; bit--) cells += '<i class="' + (((x >> bit) & 1) ? 'f' : '') + '"></i>';
        }
        var pct = (flips / 256 * 100).toFixed(1);
        out.innerHTML = '<div class="grid g3" style="margin-top:1.25rem"><div class="card white sm"><div class="stat">' + flips + '</div><div class="stat-l">of 256 bits flipped</div></div><div class="card white sm"><div class="stat">' + pct + '%</div><div class="stat-l">expected ≈ 50%</div></div><div class="card white sm"><div class="stat">' + (a === b ? 'Same' : 'Different') + '</div><div class="stat-l">inputs</div></div></div>' +
          (a === b ? '<div class="notice warn" style="margin-top:1rem">Both inputs are identical, so the digests are identical and no bits differ. Change one character.</div>' : '') +
          '<div class="grid g2" style="margin-top:1rem"><div><label>Original digest</label><span class="hash">' + ha + '</span></div><div><label>Modified digest (differing hex digits marked)</label><span class="hash">' + hl + '</span></div></div>' +
          '<label style="margin-top:1.25rem">Bit map: orange cells are bits that flipped</label><div class="bitgrid" role="img" aria-label="' + flips + ' of 256 bits differ">' + cells + '</div>';
      }).catch(function (err) { out.innerHTML = '<div class="notice bad">' + esc(err.message) + '</div>'; });
    });
    $('#avalancheForm').dispatchEvent(new Event('submit', { cancelable: true }));
  }

  /* ================= 06 security calculator ================= */
  function initSecurity() {
    var f = $('#calc');
    function upd() {
      var len = +$('#cLen').value, cs = +$('#cSet').value, rate = +$('#cRate').value;
      $('#cLenV').textContent = len + ' characters';
      var space = Math.pow(cs, len), sec = space / 2 / rate;
      $('#cOut').innerHTML = '<div class="stat">' + human(sec) + '</div><div class="stat-l">average time to find the password · ' + space.toExponential(2) + ' combinations</div>';
    }
    f.addEventListener('input', upd); upd();
  }

  var map = { hashing: initHashing, salt: initSalt, verification: initVerification, comparison: initComparison, avalanche: initAvalanche, security: initSecurity };
  BL.shell({ mod: 2 });
  if (map[page]) map[page]();
})();
