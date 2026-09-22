import { action } from '../../leanreact/engine/runtime/actions.mjs';
import { ctor } from '../../leanreact/engine/adapters/leanjs-react.mjs';
import {
  credentialHeaders,
  discardUnbound,
  normalizeOrigin,
  readBoundSession,
  saveBoundSession,
  sessionRecordKey,
} from './origin.mjs';

const ok = value => ctor('Except.ok', [value]);
const err = value => ctor('Except.error', [value]);
const none = ctor('Option.none');
const some = value => ctor('Option.some', [value]);
const nat = value => BigInt(value);
const text = value => (value == null ? '' : String(value));

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

function admittedText(look) {
  if (look?.outcome === 'flagged') return 'time';
  if (look?.admitted === false) return 'no';
  if (look?.admitted === true) return 'yes';
  return '';
}

async function call(base, path, { method = 'GET', token, boundOrigin, body } = {}) {
  const prepared = credentialHeaders({ boundOrigin, requestBase: base, path, token });
  if (!prepared.ok) return err('This session is not for that server.');
  const headers = { ...prepared.headers };
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
  return ok(payload);
}

export function loadSession(base) {
  const origin = normalizeOrigin(base);
  if (!origin) return none;
  try {
    discardUnbound(sessionStorage);
    const saved = readBoundSession(sessionStorage, origin);
    if (!saved) return none;
    return some(sessionToLean(saved.name, saved.token));
  } catch {
    return none;
  }
}

export function createApi(base) {
  const origin = normalizeOrigin(base);
  const auth = (session) => ({ token: session.fields[1], boundOrigin: origin });
  const remember = (name, token) => {
    if (origin) saveBoundSession(sessionStorage, origin, name, token);
  };
  return ctor('LeanChess.Ui.Api.mk', [
    name => action(async () => {
      const result = await call(base, '/users', { method: 'POST', body: { name } });
      if (result.tag !== 'Except.ok') return result;
      const body = result.fields[0];
      remember(body.name, body.token);
      return ok(sessionToLean(body.name, body.token));
    }),
    action(() => {
      discardUnbound(sessionStorage);
      if (origin) sessionStorage.removeItem(sessionRecordKey(origin));
    }),
    (session, opponent) => action(async () => {
      const result = await call(base, '/games', {
        method: 'POST', ...auth(session), body: { opponent },
      });
      return result.tag === 'Except.ok' ? ok(gameToLean(result.fields[0], '')) : result;
    }),
    (session, id) => action(async () => {
      const result = await call(base, `/games/${encodeURIComponent(id)}`, auth(session));
      return result.tag === 'Except.ok' ? ok(gameToLean(result.fields[0], '')) : result;
    }),
    (session, id, kind, from, to, promotion) => action(async () => {
      const body = { kind };
      if (from) body.from = from;
      if (to) body.to = to;
      if (promotion) body.promotion = promotion;
      const result = await call(base, `/games/${id}/acts`, {
        method: 'POST', ...auth(session), body,
      });
      if (result.tag !== 'Except.ok') return result;
      return ok(gameToLean(result.fields[0], admittedText(result.fields[0].look)));
    }),
    (session, id, onGame) => action(async () => {
      let stopped = false;
      const pull = async () => {
        if (stopped) return;
        const result = await call(base, `/games/${id}`, auth(session));
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
        ...auth(session),
        body: { bot: true, color, rated: false },
      });
      return result.tag === 'Except.ok' ? ok(gameToLean(result.fields[0], '')) : result;
    }),
  ]);
}
