import { createRoot } from 'react-dom/client';
import { mountElement, ctor } from '../../leanreact/engine/adapters/leanjs-react.mjs';
import * as ui from '../generated/ui.mjs';
import { createApi, loadSession } from './api.mjs';

const base = new URLSearchParams(location.search).get('api') ?? 'http://127.0.0.1:8765';
const props = ctor('LeanChess.Ui.Props.mk', [createApi(base), loadSession()]);
createRoot(document.getElementById('root')).render(mountElement(ui['LeanChess.Ui.App'], props));
