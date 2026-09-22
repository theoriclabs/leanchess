import { createRoot } from 'react-dom/client';
import { mountElement, ctor } from '../../leanreact/engine/adapters/leanjs-react.mjs';
import * as ui from '../generated/ui.mjs';
import { createApi, loadSession } from './api.mjs';

const asked = new URLSearchParams(location.search).get('api');
const local = location.hostname === '127.0.0.1' || location.hostname === 'localhost';
const base = asked ?? (local ? 'http://127.0.0.1:8765' : location.origin);
const props = ctor('LeanChess.Ui.Props.mk', [createApi(base), loadSession()]);
createRoot(document.getElementById('root')).render(mountElement(ui['LeanChess.Ui.App'], props));
