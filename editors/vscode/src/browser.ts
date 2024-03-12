import { ExtensionContext } from "vscode";
import { LanguageClient } from "vscode-languageclient/browser";
import { activateClientLSP, deactivateClientLSP} from "./client"; //, ClientFactoryType

export function activate(context: ExtensionContext): void {
  // const cf: ClientFactoryType = (context, clientOptions, wsConfig) => {
  //   // Pending on having the API to fetch the worker file.
  //   throw "Worker not found";
  //   let worker = new Worker("");
  //   return new LanguageClient(
  //     "lambdapi",
  //     "lambdapi language server",
  //     clientOptions,
  //     worker
  //   );
  // };
  activateClientLSP(context);
}

export function deactivate() {
  deactivateClientLSP();
}
