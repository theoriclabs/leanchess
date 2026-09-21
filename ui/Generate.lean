import LeanReact.Compiler
import ui.App

def uiOptions : LeanJS.Options :=
  let base := LeanReact.Compiler.options "../../leanreact/engine/adapters/leanjs-react.mjs"
  -- The board is a fixed tree of squares. The hook checker walks it.
  { base with hooks := { base.hooks with fuel := 2000000 } }

run_meta do
  IO.FS.createDirAll "generated"
  LeanJS.writeModule "generated/ui.mjs"
    #[`LeanChess.Ui.App, `LeanChess.Ui.Props.mk, `LeanChess.Ui.Api.mk,
      `LeanChess.Ui.Session.mk, `LeanChess.Ui.Game.mk, `LeanChess.Ui.Look.mk,
      `LeanChess.Ui.PieceView.mk]
    uiOptions
