import { ExtensionContext, window } from "vscode";
import { LanguageClient } from "vscode-languageclient/node";
import { activateClientLSP, ClientFactoryType, deactivateClientLSP } from "./client";

export function activate(context: ExtensionContext): void {
  const cf: ClientFactoryType = (context, clientOptions, wsConfig, lspServerPath) => {
    let serverOptions = {
      command: lspServerPath,
      args: ['lsp']
    };
    return new LanguageClient(
      "lambdapi",
      "lambdapi language server",
      serverOptions,
      clientOptions);
  };
  activateClientLSP(context, cf);
}

export function deactivate() {
  deactivateClientLSP();
}
