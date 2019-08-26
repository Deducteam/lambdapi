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
let panel : WebviewPanel;
let inset : WebviewEditorInset;

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

		//create and show panel
		panel = window.createWebviewPanel(
			'goals',
			'Goals',
			ViewColumn.Two,
			{}
		);  
			
				
		window.onDidChangeActiveTextEditor(e => {
			
			restartPanel();
			window.showInformationMessage('Going to start!');
			window.onDidChangeTextEditorSelection(e => {
				let selec = e.textEditor.selection;
				sendGoalsRequest(e.textEditor,selec.active);
			});

		});
			
	context.subscriptions.push(
		commands.registerCommand('getGoals.start', () => {
			
		})

	);


	});

}

function restartPanel(){

	panel.webview.html = getWebviewContent("");

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

	function sendGoalsRequest(editor : TextEditor, position: Position) {
		let goalsState : String;
		
		let uri = editor.document.uri;
		let doc = {uri : uri.toString()}
		let cursor = {textDocument : doc, position : position}; 
		const req = new RequestType<ParamsGoals, GoalResp, void, void>("proof/goals");
		
		client.sendRequest(req, cursor).then((goals) => {
			let a = goals.contents;
			let line = position.line;
			let height = 5;
		
			//return goals;
			let result = getWebviewContent(a);
			
			//display goals in webviewTextEditor
			if(disposables.length > 0) {
				let x = disposables.pop();
				if(x) x.dispose();
			}
			let inset = window.createWebviewTextEditorInset(editor, line, height);
			disposables.push(inset);
			inset.webview.html = result;
			panel.webview.html = result;
			
		}, _ => {
			panel.webview.html = getWebviewContent("");
		}); 
	}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
