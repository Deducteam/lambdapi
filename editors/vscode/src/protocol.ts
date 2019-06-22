    //import language client
    //language server extension guide
    //see debugging cleint side server side
    //isabelle repository vscode extension protocol.ts
    // see notification type
    //promise javascript when we send command to the server 
    //when the command is ready then  we display the goals
    //looo at cursor how to get the position of the cursor an moving it ondidchangetexteditorselection
    // see the extension vscode of coq more important thant isabelle

//language server
/*let client = new LanguageClient(...);
client.onReady().then(() => {
  client.onNotification(...);
  client.sendRequest(...);
);*/
//webView
import * as vscode from 'vscode';

export function activate(context: vscode.ExtensionContext) {
  context.subscriptions.push(
    vscode.commands.registerCommand('vscode-lp.restart', () => {
      // Create and show a new webview
      const panel = vscode.window.createWebviewPanel(
        'goals', // Identifies the type of the webview. Used internally
        'Goals', // Title of the panel displayed to the user
        vscode.ViewColumn.Two, // Editor column to show the new webview panel in.
        {} // Webview options. More on these later.
      );
      // And set its HTML content
      panel.webview.html = getWebviewContent();
    })
  );
}

function getWebviewContent() {
  return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Cat Coding</title>
</head>
<body>
    <--! afficher les goals-->
    <p>  hello LSP</p>
</body>
</html>`;
}