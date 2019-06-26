// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as path from 'path';
import * as vscode from 'vscode';
//import { NotificationType, RequestType } from 'vscode-languageclient';
import {
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	TransportKind,
	NotificationType,
	RequestType
  } from 'vscode-languageclient';


let client: LanguageClient;

// this method is called when your extension is activated
// your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {

	// The server is implemented in node
	let serverModule = context.asAbsolutePath(path.join('server', 'out', 'server.js'));
	// The debug options for the server
	// --inspect=6009: runs the server in Node's Inspector mode so VS Code can attach to the server for debugging
	let debugOptions = { execArgv: ['--nolazy', '--inspect=6009'] };
  
	// If the extension is launched in debug mode then the debug server options are used
	// Otherwise the run options are used
	let serverOptions: ServerOptions = {
	  run: { module: serverModule, transport: TransportKind.ipc },
	  debug: {
		module: serverModule,
		transport: TransportKind.ipc,
		options: debugOptions
	  }
	}
	// Options to control the language client
	let clientOptions: LanguageClientOptions = {
	  // Register the server for plain text documents
	  documentSelector: [{ scheme: 'file', language: 'lp' }],
	  synchronize: {
		// Notify the server about file changes to '.clientrc files contained in the workspace
		fileEvents: vscode.workspace.createFileSystemWatcher('**/.clientrc')
	  }
	};
  
	// Create the language client and start the client.
	client = new LanguageClient(
	  'lambdapi',
	  'Language Server Example',
	  serverOptions,
	  clientOptions
	);
  
	// Start the client. This will also launch the server
	client.start();





	context.subscriptions.push(
	  vscode.commands.registerCommand('getGoals.start', () => {
		// Create and show panel
		const panel = vscode.window.createWebviewPanel(
		  'goals',
		  'Goals',
		  vscode.ViewColumn.Two,
		  {}
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
	  <p> print the goals </p>
  </body>
  </html>`;
  }