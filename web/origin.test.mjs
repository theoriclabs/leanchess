import assert from 'node:assert/strict';
import test from 'node:test';
import {
  credentialHeaders,
  discardUnbound,
  legacySessionKey,
  normalizeOrigin,
  readBoundSession,
  requestOrigin,
  resolveApiBase,
  saveBoundSession,
  sessionRecordKey,
} from './origin.mjs';

function memory() {
  const map = new Map();
  return {
    getItem: (key) => (map.has(key) ? map.get(key) : null),
    setItem: (key, value) => { map.set(key, String(value)); },
    removeItem: (key) => { map.delete(key); },
    keys: () => [...map.keys()],
  };
}

test('production ignores a crafted api query', () => {
  const page = 'https://play.example';
  assert.equal(resolveApiBase({
    pageOrigin: page,
    hostname: 'play.example',
    apiParam: 'https://evil.example/steal',
  }), page);
  assert.equal(resolveApiBase({
    pageOrigin: page,
    hostname: 'play.example',
    apiParam: 'http://127.0.0.1:8765',
  }), page);
});

test('loopback may select another loopback origin, and nothing else', () => {
  assert.equal(resolveApiBase({
    pageOrigin: 'http://localhost:4173',
    hostname: 'localhost',
    apiParam: null,
  }), 'http://127.0.0.1:8765');
  assert.equal(resolveApiBase({
    pageOrigin: 'http://127.0.0.1:4173',
    hostname: '127.0.0.1',
    apiParam: 'http://127.0.0.1:9999/api',
  }), 'http://127.0.0.1:9999');
  assert.equal(resolveApiBase({
    pageOrigin: 'http://localhost:4173',
    hostname: 'localhost',
    apiParam: 'https://evil.example',
  }), 'http://127.0.0.1:8765');
  assert.equal(resolveApiBase({
    pageOrigin: 'http://localhost:4173',
    hostname: 'localhost',
    apiParam: 'http://127.0.0.1:8765@evil.example',
  }), 'http://127.0.0.1:8765');
  assert.equal(resolveApiBase({
    pageOrigin: 'http://localhost:4173',
    hostname: 'localhost',
    apiParam: 'javascript:alert(1)',
  }), 'http://127.0.0.1:8765');
});

test('origin normalization drops path, query, and userinfo', () => {
  assert.equal(normalizeOrigin('http://127.0.0.1:8765/extra?x=1#y'), 'http://127.0.0.1:8765');
  assert.equal(normalizeOrigin('http://ada:secret@127.0.0.1:8765/'), 'http://127.0.0.1:8765');
  assert.equal(normalizeOrigin('not a url'), null);
});

test('an unbound session is deleted and not forwarded', () => {
  const store = memory();
  store.setItem(legacySessionKey, JSON.stringify({ name: 'ada', token: 'secret' }));
  discardUnbound(store);
  assert.equal(store.getItem(legacySessionKey), null);
  assert.equal(readBoundSession(store, 'https://evil.example'), null);
  assert.equal(readBoundSession(store, 'http://127.0.0.1:8765'), null);
  assert.deepEqual(store.keys(), []);
});

test('reload returns the token only for its issuer', () => {
  const store = memory();
  const home = 'http://127.0.0.1:8765';
  const other = 'http://127.0.0.1:9999';
  saveBoundSession(store, home, 'ada', 'home-token');
  assert.equal(readBoundSession(store, home).token, 'home-token');
  assert.equal(readBoundSession(store, other), null);
  saveBoundSession(store, other, 'ada', 'other-token');
  assert.equal(readBoundSession(store, home).token, 'home-token');
  assert.equal(readBoundSession(store, other).token, 'other-token');
});

test('a record whose audience is not the issuer is refused', () => {
  const store = memory();
  const home = 'http://127.0.0.1:8765';
  store.setItem(sessionRecordKey(home), JSON.stringify({
    name: 'ada', token: 'secret', iss: home, aud: 'https://evil.example',
  }));
  assert.equal(readBoundSession(store, home), null);
});

test('no authorization header is built for a mismatched destination', () => {
  const home = 'http://127.0.0.1:8765';
  const matched = credentialHeaders({
    boundOrigin: home,
    requestBase: home,
    path: '/games/1/acts',
    token: 'home-token',
  });
  assert.equal(matched.ok, true);
  assert.equal(matched.headers.authorization, 'Bearer home-token');

  const crafted = credentialHeaders({
    boundOrigin: home,
    requestBase: 'https://evil.example',
    path: '/games/1/acts',
    token: 'home-token',
  });
  assert.equal(crafted.ok, false);
  assert.equal('authorization' in crafted.headers, false);
  assert.equal(requestOrigin('https://evil.example', '/games/1/acts'), 'https://evil.example');
});
