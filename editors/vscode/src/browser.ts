import { ExtensionContext } from "vscode";
import { LanguageClient } from "vscode-languageclient/browser";
import { activateClientLSP, ClientFactoryType, deactivateClientLSP} from "./client";

export function activate(context: ExtensionContext): void {
  const cf: ClientFactoryType = (context, clientOptions, wsConfig) => {
    // Pending on having the API to fetch the worker file.
    throw "Worker not found";
    let worker = new Worker("");
    return new LanguageClient(
      "lambdapi",
      "lambdapi language server",
      clientOptions,
      worker
    );
  };
  activateClientLSP(context, cf);
}

export function deactivate() {
  deactivateClientLSP();
}
