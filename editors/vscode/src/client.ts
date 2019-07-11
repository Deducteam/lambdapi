/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import * as path from 'path';
import { workspace, ExtensionContext, Position, Uri, commands, window, WebviewPanel, ViewColumn, TextEditor } from 'vscode';


import {
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	TransportKind,
	RequestType,
	NotificationType
} from 'vscode-languageclient';



let client: LanguageClient;

export function activate(context: ExtensionContext) {
	// The server is implemented in node
	let serverModule = context.asAbsolutePath(
		path.join('..', '..', 'lp-lsp', 'lp_lsp.ml')
		//path.join('server', 'out', 'server.js')
	);
	
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
	};

	// Options to control the language client
	let clientOptions: LanguageClientOptions = {
		// Register the server for plain text documents
		documentSelector: [{ scheme: 'file', language: 'lp' }],
		synchronize: {
			// Notify the server about file changes to '.clientrc files contained in the workspace
			fileEvents: workspace.createFileSystemWatcher('**/.clientrc')
		}
	};

	// Create the language client and start the client.
	client = new LanguageClient(
		'languageServerExample',
		'Language Server Example',
		serverOptions,
		clientOptions
	);
	
	// Start the client. This will also launch the server
	client.start();

	//display goals
	//onselectionchange sendgoalsrequest

	client.onReady().then(() => {

	context.subscriptions.push(
		commands.registerCommand('getGoals.start', () => {

		  workspace.onDidOpenTextDocument(_ => {
			const editor = window.activeTextEditor;
			
			const doc = editor == undefined? null : editor.document; 
			const selec = editor == undefined? null : editor.selection;
			const uri = doc == null? null : doc.uri;
			if(doc != null){
				window.showTextDocument(doc, ViewColumn.One);
			}
			
			//client.sendNotification(notifOpen, uri);
			if(uri != null){
				const notifOpen = new NotificationType<Uri, void>("textDocument/didOpen");
				client.sendNotification(notifOpen, uri);

				//send initialize

				const notifChange = new NotificationType<Uri, void>("textDocument/didChange");
				client.sendNotification(notifChange, uri);
			}
			

			

		  // Create and show panel
			
			const panel = window.createWebviewPanel(
				'goals',
				'Goals',
				ViewColumn.Two,
				{}
			);
		
			// And set its HTML content
			panel.webview.html = getWebviewContent("");
			window.onDidChangeTextEditorSelection(e => {
				if (selec != null && uri != null){
					sendGoalsRequest(selec.active, panel, uri)
				} 
			}
				);
				
			if(uri != null){
				const notifClose = new NotificationType<Uri, void>("textDocument/didClose");
				client.sendNotification(notifClose, uri);
			}
			
	
			
			});	

			
		})

	  );
	});
	}
	
	function getWebviewContent(goals : String) {
		let goalsPrint : string;
		let htmlPage1 : string;
		let htmlPage2 : string;
		goalsPrint = goals == null? `` : goals.toString(); 
		htmlPage1 =  `<!DOCTYPE html>
		<html lang="en">
		<head>
			<meta charset="UTF-8">
			<meta name="viewport" content="width=device-width, initial-scale=1.0">
			<title> Goals</title>
		</head>
		<body>
			<p> `; 
		htmlPage2 =	` </p>
		</body>
		</html>`;

		return htmlPage1.concat(goalsPrint.concat(htmlPage2));
	}
		
export interface ParamsGoals {
	uri : Uri
	line : number
	character : number
}

	function sendGoalsRequest(position: Position, panel : WebviewPanel, uri : Uri){
		let goalsState : String;
		let cursor = {uri : uri, line : position.line, character : position.character}; 
		//---client.onRequest(new RequestType("../../../../../lp-lsp/lp-lsp/getGoals", caret, string))
		const req = new RequestType<ParamsGoals, String, void, void>("proof/goals");
		client.sendRequest(req, cursor).then((goals) => {
		//return goals
		return goals;
		//panel.webview.html = getWebviewContent(goals);
		}); 
	}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}

