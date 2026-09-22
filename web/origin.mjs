/*
  Where a saved token may be sent.

  A credential is bound to the normalized origin that issued it. That
  origin is both issuer and audience. An authenticated request is
  refused before it is constructed when the destination origin differs.

  Production uses the page origin. `?api=` cannot retarget it.

  On a loopback page, `?api=` may select another loopback origin. That
  choice is a different session. It does not receive a token minted for
  the previous origin. A saved record with no issuer is deleted and is
  not copied onto the newly selected origin.
*/

export const legacySessionKey = 'leanchess.session';
export const devApiOrigin = 'http://127.0.0.1:8765';

export function isLocalHost(hostname) {
  const host = String(hostname ?? '').toLowerCase().replace(/^\[|\]$/g, '');
  return host === 'localhost' || host === '127.0.0.1' || host === '::1';
}

export function normalizeOrigin(value) {
  if (typeof value !== 'string' || value.trim() === '') return null;
  let url;
  try {
    url = new URL(value);
  } catch {
    return null;
  }
  if (url.protocol !== 'http:' && url.protocol !== 'https:') return null;
  return url.origin;
}

export function resolveApiBase({ pageOrigin, hostname, apiParam }) {
  const page = normalizeOrigin(pageOrigin);
  if (!isLocalHost(hostname)) return page ?? String(pageOrigin ?? '');
  if (apiParam == null || String(apiParam).trim() === '') return devApiOrigin;
  const selected = normalizeOrigin(apiParam);
  if (!selected) return devApiOrigin;
  let host = '';
  try {
    host = new URL(selected).hostname;
  } catch {
    return devApiOrigin;
  }
  if (!isLocalHost(host)) return devApiOrigin;
  return selected;
}

export function sessionRecordKey(origin) {
  return `leanchess.session.v2:${origin}`;
}

export function discardUnbound(storage) {
  if (storage.getItem(legacySessionKey) != null) storage.removeItem(legacySessionKey);
}

export function saveBoundSession(storage, origin, name, token) {
  const record = { name, token, iss: origin, aud: origin };
  storage.setItem(sessionRecordKey(origin), JSON.stringify(record));
  return record;
}

export function readBoundSession(storage, origin) {
  const key = sessionRecordKey(origin);
  let parsed;
  try {
    parsed = JSON.parse(storage.getItem(key) ?? 'null');
  } catch {
    return null;
  }
  if (!parsed || typeof parsed !== 'object') return null;
  if (parsed.iss !== origin || parsed.aud !== origin) return null;
  if (!parsed.name || !parsed.token) return null;
  return parsed;
}

export function requestOrigin(base, path) {
  try {
    const root = base.endsWith('/') ? base : `${base}/`;
    return new URL(path, root).origin;
  } catch {
    return null;
  }
}

/** Headers for one request. `ok: false` means do not send it authenticated. */
export function credentialHeaders({ boundOrigin, requestBase, path, token }) {
  if (!token) return { ok: true, headers: {} };
  const dest = requestOrigin(requestBase, path);
  if (!boundOrigin || !dest || dest !== boundOrigin) return { ok: false, headers: {} };
  return { ok: true, headers: { authorization: `Bearer ${token}` } };
}
