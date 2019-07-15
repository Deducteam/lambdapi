/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import * as path from 'path';
import * as fs from 'fs';
import * as net from 'net';
import * as child_process from 'child_process';
import { workspace, ExtensionContext, Position, Uri, commands, window, WebviewPanel, ViewColumn, TextEditor, TextDocument } from 'vscode';


import {
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	TransportKind,
	RequestType,
	NotificationType,
	TextDocumentIdentifier,
} from 'vscode-languageclient';



let client: LanguageClient;

export function activate(context: ExtensionContext) {

	//create the server
	

	// The server is implemented in node
	//let serverModule = context.asAbsolutePath(
	//	path.join('..', '..', 'lp-lsp', 'lp_lsp.ml')
	//	//path.join('server', 'out', 'server.js')
	//);
	
	// The debug options for the server
	// --inspect=6009: runs the server in Node's Inspector mode so VS Code can attach to the server for debugging
	//let debugOptions = { execArgv: ['--nolazy', '--inspect=6009'] };

	// If the extension is launched in debug mode then the debug server options are used
	// Otherwise the run options are used
	//let serverOptions: ServerOptions = {
	//	run: { module: serverModule, transport: TransportKind.ipc },
	//	debug: {
	//		module: serverModule,
	//		transport: TransportKind.ipc,
	//		options: debugOptions
	//	}
	//};

	let serverOptions = {
		command: '/Users/houdamouzoun/.opam/4.05.0/bin/lp-lsp',
		args: [ '--std' ]
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

		const editor = window.activeTextEditor;
			
			const doc = editor == undefined? null : editor.document; 
			const selec = editor == undefined? null : editor.selection;
			const uri = doc == null? null : doc.uri;

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
				

	context.subscriptions.push(
		commands.registerCommand('getGoals.start', () => {
			// TO delete redundant code
		  /*workspace.onDidOpenTextDocument(_ => {
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
			
			
			

			const editor = window.activeTextEditor;
			
			const doc = editor == undefined? null : editor.document; 
			const selec = editor == undefined? null : editor.selection;
			const uri = doc == null? null : doc.uri;

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
			*/
			
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

export interface TextDocumentIdent{
	uri : String
}	

export interface ParamsGoals {
	textDocument : TextDocumentIdent
	position : Position
}

	function sendGoalsRequest(position: Position, panel : WebviewPanel, uri : Uri){
		let goalsState : String;
		let doc = {uri : uri.toString()}
		let cursor = {textDocument : doc, position : position}; 
		const req = new RequestType<ParamsGoals, String, void, void>("proof/goals");
		client.sendRequest(req, cursor).then((goals) => {
		//return goals;
		panel.webview.html = getWebviewContent(goals);
		}); 
	}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}

