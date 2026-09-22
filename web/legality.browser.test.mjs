// The page's legality is the domain's `legalMoves`. Run against a server
// that serves the built page:
//   .lake/build/bin/leanchess-api --web web/dist --port 18767 --db /tmp/lc-browser.sqlite
//   PLAYWRIGHT=../leanreact/node_modules/playwright/index.mjs node web/legality.browser.test.mjs
import assert from 'node:assert/strict';

const { chromium } = await import(process.env.PLAYWRIGHT ?? 'playwright');
const base = process.env.LEANCHESS_URL ?? 'http://127.0.0.1:18767';
const run = Date.now().toString(36);

async function api(path, { token, body } = {}) {
  const headers = { 'content-type': 'application/json' };
  if (token) headers.authorization = `Bearer ${token}`;
  const response = await fetch(`${base}${path}`, {
    method: body === undefined ? 'GET' : 'POST',
    headers,
    body: body === undefined ? undefined : JSON.stringify(body),
  });
  return response.json();
}

const black = await api('/users', { body: { name: `black-${run}` } });
assert.ok(black.ok, 'register the black seat');

const browser = await chromium.launch();
const page = await browser.newPage();
let acts = 0;
page.on('request', request => {
  if (request.method() === 'POST' && request.url().endsWith('/acts')) acts += 1;
});

// A loopback page talks to the dev API unless `?api=` names this server.
await page.goto(`${base}/?api=${encodeURIComponent(base)}`);
await page.fill('#name', `white-${run}`);
await page.getByRole('button', { name: 'Take a seat' }).click();

const square = sq => page.getByRole('button', { name: sq, exact: true });
// A square's text also carries its coordinate on the board's edges; the piece is the glyph.
const glyphOf = text => (text.match(/[\u2654-\u265F]/) ?? [''])[0];
const glyphOn = async sq => glyphOf(await square(sq).innerText());
const targets = async sq => {
  await square(sq).click();
  const marked = await page.locator('.sq.target').evaluateAll(els => els.map(el => el.getAttribute('aria-label')));
  return marked.sort();
};

async function newGame() {
  const leave = page.getByRole('button', { name: 'Leave this board' });
  if (await leave.count()) await leave.click();
  await page.fill('#opponent', `black-${run}`);
  await page.locator('form.card', { hasText: 'Play a person' }).getByRole('button', { name: 'Start' }).click();
  const label = await page.locator('.card.quiet .fine').innerText();
  return Number(label.match(/game (\d+)/)[1]);
}

async function play(id, line) {
  for (const [i, move] of line.entries()) {
    const [from, to] = [move.slice(0, 2), move.slice(2, 4)];
    if (i % 2 === 0) {
      await square(from).click();
      await square(to).click();
    } else {
      const r = await api(`/games/${id}/acts`, { token: black.token, body: { kind: 'play', from, to } });
      assert.equal(r.look?.admitted, true, `black ${move}`);
    }
    await page.waitForFunction(([f, t]) => {
      const cell = sq => (document.querySelector(`[aria-label="${sq}"]`)?.textContent.match(/[\u2654-\u265F]/) ?? [''])[0];
      return cell(f) === '' && cell(t) !== '';
    }, [from, to]);
  }
}

// The opening: two squares for a pawn, and a drop elsewhere never leaves the page.
{
  await newGame();
  assert.deepEqual(await targets('e2'), ['e3', 'e4']);
  assert.deepEqual(await targets('g1'), ['f3', 'h3']);
  await square('e2').click();
  const before = acts;
  await square('e5').click();
  await page.getByText('Not a legal move.').waitFor();
  assert.equal(acts, before, 'an illegal drop sends nothing');
  assert.equal(await glyphOn('e2'), '♙', 'the board is unchanged');
}

// A pinned knight has nowhere to go.
{
  const id = await newGame();
  await play(id, ['d2d4', 'e7e5', 'b1c3', 'f8b4']);
  assert.deepEqual(await targets('c3'), [], 'Nc3 is pinned by Bb4');
}

// En passant is offered on the move after the double step.
{
  const id = await newGame();
  await play(id, ['e2e4', 'a7a6', 'e4e5', 'd7d5']);
  assert.deepEqual(await targets('e5'), ['d6', 'e6']);
}

// Castling does not cross an attacked square; the same shape without the
// bishop on a6 castles.
{
  const id = await newGame();
  await play(id, ['g2g3', 'b7b6', 'g1f3', 'c8a6', 'f1h3', 'b8c6', 'e2e3', 'g8f6']);
  const t = await targets('e1');
  assert.ok(!t.includes('g1'), `f1 is attacked, so no castling: ${t}`);
  assert.ok(!t.includes('f1') && !t.includes('e2'), `the king does not step into the bishop: ${t}`);
}
{
  const id = await newGame();
  await play(id, ['g2g3', 'a7a6', 'g1f3', 'b7b6', 'f1h3', 'c7c6', 'e2e3', 'd7d6']);
  assert.ok((await targets('e1')).includes('g1'), 'castling is offered');
}

// A promotion asks for the piece; the choice is what lands.
{
  const id = await newGame();
  await play(id, ['h2h4', 'g7g5', 'h4g5', 'f7f6', 'g5f6', 'g8h6', 'f6e7', 'h6g8']);
  await square('e7').click();
  await square('f8').click();
  await page.getByRole('group', { name: 'Promote to' }).waitFor();
  await page.getByRole('button', { name: 'knight', exact: true }).click();
  await page.waitForFunction(() => document.querySelector('[aria-label="f8"]')?.textContent.includes('♘'));
}

await browser.close();
console.log('legality in the browser: ok');
