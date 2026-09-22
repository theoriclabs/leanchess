import { action } from '../../leanreact/engine/runtime/actions.mjs';
import { ctor } from '../../leanreact/engine/adapters/leanjs-react.mjs';

const ok = value => ctor('Except.ok', [value]);
const err = value => ctor('Except.error', [value]);
const none = ctor('Option.none');
const some = value => ctor('Option.some', [value]);
const nat = value => BigInt(value);
const text = value => (value == null ? '' : String(value));

const sessionKey = 'leanchess.session';

function sessionToLean(name, token) {
  return ctor('LeanChess.Ui.Session.mk', [name, token]);
}

function pieceToLean(piece) {
  return ctor('LeanChess.Ui.PieceView.mk', [piece.square, piece.color, piece.kind]);
}

function gameToLean(body, admitted) {
  const look = body.look ?? {};
  return ctor('LeanChess.Ui.Game.mk', [
    nat(body.id),
    text(body.white),
    text(body.black),
    ctor('LeanChess.Ui.Look.mk', [
      text(look.ending),
      text(look.turn),
      text(look.offer),
      nat(look.whiteLeft ?? 0),
      nat(look.blackLeft ?? 0),
      nat(look.ply ?? 0),
      text(look.you),
      admitted,
      (look.board ?? []).map(pieceToLean),
      look.check === true ? 'yes' : '',
      text(look.movedFrom),
      text(look.movedTo),
    ]),
  ]);
}

const clock = { server: 0n, local: 0 };

function noteClock(body) {
  if (body?.now == null) return;
  clock.server = BigInt(body.now);
  clock.local = Date.now();
}

function atNow() {
  const elapsed = BigInt(Math.max(0, Date.now() - clock.local));
  return clock.server + elapsed;
}

async function call(base, path, { method = 'GET', token, body } = {}) {
  const headers = {};
  if (token) headers.authorization = `Bearer ${token}`;
  if (body !== undefined) headers['content-type'] = 'application/json';
  let response;
  try {
    response = await fetch(`${base}${path}`, {
      method,
      headers,
      body: body === undefined ? undefined : JSON.stringify(body),
    });
  } catch {
    return err('The server is not reachable.');
  }
  let payload = {};
  try { payload = await response.json(); } catch { /* a non-JSON body is still a failure */ }
  if (!response.ok || payload.ok === false) return err(text(payload.error) || `The server answered ${response.status}.`);
  noteClock(payload);
  return ok(payload);
}

export function loadSession() {
  try {
    const saved = JSON.parse(sessionStorage.getItem(sessionKey) ?? 'null');
    if (!saved?.name || !saved?.token) return none;
    return some(sessionToLean(saved.name, saved.token));
  } catch {
    return none;
  }
}

export function createApi(base) {
  const remember = (name, token) => sessionStorage.setItem(sessionKey, JSON.stringify({ name, token }));
  return ctor('LeanChess.Ui.Api.mk', [
    name => action(async () => {
      const result = await call(base, '/users', { method: 'POST', body: { name } });
      if (result.tag !== 'Except.ok') return result;
      const body = result.fields[0];
      remember(body.name, body.token);
      return ok(sessionToLean(body.name, body.token));
    }),
    action(() => { sessionStorage.removeItem(sessionKey); }),
    (session, opponent) => action(async () => {
      const result = await call(base, '/games', {
        method: 'POST', token: session.fields[1], body: { opponent },
      });
      return result.tag === 'Except.ok' ? ok(gameToLean(result.fields[0], '')) : result;
    }),
    (session, id) => action(async () => {
      const result = await call(base, `/games/${encodeURIComponent(id)}`, { token: session.fields[1] });
      return result.tag === 'Except.ok' ? ok(gameToLean(result.fields[0], '')) : result;
    }),
    (session, id, kind, from, to, promotion) => action(async () => {
      const body = { kind, at: Number(atNow()) };
      if (from) body.from = from;
      if (to) body.to = to;
      if (promotion) body.promotion = promotion;
      const result = await call(base, `/games/${id}/acts`, {
        method: 'POST', token: session.fields[1], body,
      });
      if (result.tag !== 'Except.ok') return result;
      const admitted = result.fields[0].look?.admitted === false ? 'no' : 'yes';
      return ok(gameToLean(result.fields[0], admitted));
    }),
    (session, id, onGame) => action(async () => {
      let stopped = false;
      const pull = async () => {
        if (stopped) return;
        const result = await call(base, `/games/${id}?at=${atNow()}`, { token: session.fields[1] });
        if (stopped || result.tag !== 'Except.ok') return;
        const update = onGame(gameToLean(result.fields[0], ''));
        await update.execute();
      };
      await pull();
      const timer = setInterval(pull, 500);
      return action(() => { stopped = true; clearInterval(timer); });
    }),
    (session, color) => action(async () => {
      const result = await call(base, '/games', {
        method: 'POST',
        token: session.fields[1],
        body: { bot: true, color, rated: false },
      });
      return result.tag === 'Except.ok' ? ok(gameToLean(result.fields[0], '')) : result;
    }),
  ]);
}
