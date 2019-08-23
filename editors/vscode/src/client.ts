/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import * as path from 'path';
import * as fs from 'fs';
import * as net from 'net';
import * as child_process from 'child_process';
import { workspace, ExtensionContext, Position, Uri, commands, window, WebviewPanel, ViewColumn, TextEditor, TextDocument, WebviewEditorInset, Disposable } from 'vscode';


import {
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	TransportKind,
	RequestType,
	NotificationType,
	TextDocumentIdentifier,
	RegistrationRequest,
} from 'vscode-languageclient';
import { isUndefined } from 'util';



let client: LanguageClient;
let disposables : Disposable[] = [];

export function activate(context: ExtensionContext) {

	//create the server

	let serverOptions = {
		command: '/Users/houdamouzoun/.opam/4.05.0/bin/lp-lsp',
		args: [ '--std' ]
	};

	// Options to control the language client
	let clientOptions: LanguageClientOptions = {
		// Register the server for lp documents
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

		  // Create and show panel
			
			const panel = window.createWebviewPanel(
				'goals',
				'Goals',
				ViewColumn.Two,
				{}
			);
			
			/*workspace.onDidOpenTextDocument(e => {
				let oldWB = disposables.pop();
				if (oldWB)
					oldWB.dispose();
				if(e.languageId === 'lp'){
					//window.showTextDocument(e, ViewColumn.One, true);
					restart(panel)
				}
			}) */
			
				
		window.onDidChangeActiveTextEditor(e => {
			let oldWB = disposables.pop();
			while(oldWB) {
				oldWB.dispose();
				oldWB = disposables.pop();
			}
			restart(panel)
		});
			
	context.subscriptions.push(
		commands.registerCommand('getGoals.start', () => {
			
		})

	);


	});

}
	

	function restart(panel : WebviewPanel){
		
			const editor = window.activeTextEditor;
			
			const doc = editor == undefined? null : editor.document; 
			const selec = editor == undefined? null : editor.selection;
			const uri = doc == null? null : doc.uri;
			// And set its HTML content
			panel.webview.html = getWebviewContent("");
			window.showInformationMessage('Going to start!');
			window.onDidChangeTextEditorSelection(e => {
				let oldWB = disposables.pop();
				while(oldWB) {
					oldWB.dispose();
					oldWB = disposables.pop();
				}
				let selec = e.textEditor.selection;
				if (uri != null){
					sendGoalsRequest(selec.active, panel, uri);
					
				} 
			}
				);
	}
	
	function getWebviewContent(goals : String) {
		let goalsPrint : String;
		let htmlPage1 : String;
		let htmlPage2 : String;
		goalsPrint = goals; 
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

		return htmlPage1+""+goalsPrint+htmlPage2;
	}

export interface TextDocumentIdent{
	uri : String
}	

export interface ParamsGoals {
	textDocument : TextDocumentIdent
	position : Position
}

export interface GoalResp {
	contents : String
}

	function sendGoalsRequest(position: Position, panel : WebviewPanel, uri : Uri) {
		let goalsState : String;
		if(window.activeTextEditor){
			let uri2 = window.activeTextEditor.document.uri.toString();
			window.showInformationMessage("active Txt Edit : "+ uri2);
		
		let doc = {uri : uri2}
		let cursor = {textDocument : doc, position : position}; 
		const req = new RequestType<ParamsGoals, GoalResp, void, void>("proof/goals");
		//let fail = {contents : ""}
		window.showInformationMessage(uri.toString()+ " line:" + position.line);
		client.sendRequest(req, cursor).then((goals) => {
		let a = goals.contents;
		let line = position.line;
		let height = 5;
	
		//return goals;
		let result = getWebviewContent(a);
		let defaultRslt = getWebviewContent("");
		
		//display goals in webviewTextEditor
		if(window.activeTextEditor && a != "") {
			if (disposables.length >= 1){
				window.showInformationMessage('one or more WEBVIEW');
				let oldWB = disposables.pop();
				while(oldWB) {
					oldWB.dispose();
					oldWB = disposables.pop();
				}
			}else {
				window.showInformationMessage('zero WEBVIEW');
			}
			let wb = window.createWebviewTextEditorInset(window.activeTextEditor, line, height);
			wb.webview.html = result;
			disposables.push(wb);
			panel.webview.html = result;
			wb.onDidDispose(() => {
				console.log('WEBVIEW disposed...');
			});

			window.showInformationMessage("there are goals");
		} else {
			panel.webview.html = defaultRslt;
			window.showInformationMessage("no goals");
		}
		}, (_)=>{
			let defaultRslt = getWebviewContent("");
			panel.webview.html = defaultRslt;
		}); 
	}
	}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
