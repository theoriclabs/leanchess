import { createRoot } from 'react-dom/client';
import { mountElement, ctor } from '../../leanreact/engine/adapters/leanjs-react.mjs';
import * as ui from '../generated/ui.mjs';
import { createApi, loadSession } from './api.mjs';
import { resolveApiBase } from './origin.mjs';

const params = new URLSearchParams(location.search);
const base = resolveApiBase({
  pageOrigin: location.origin,
  hostname: location.hostname,
  apiParam: params.get('api'),
});
const props = ctor('LeanChess.Ui.Props.mk', [createApi(base), loadSession(base)]);
createRoot(document.getElementById('root')).render(mountElement(ui['LeanChess.Ui.App'], props));
