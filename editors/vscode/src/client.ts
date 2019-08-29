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

	client.onReady().then(() => {

		//create and show panel
		panel = window.createWebviewPanel(
			'goals',
			'Goals',
			ViewColumn.Two,
			{}
		);  
			
		//update the panel 		
		window.onDidChangeActiveTextEditor(e => {
			if(e){
				if(e.document.uri.toString() !== "")
					restartPanel();
			}
		});

		window.showInformationMessage('Going to start!');
		//send goals request when the cursor's position changes
		window.onDidChangeTextEditorSelection(e => {
			let selec = e.textEditor.selection;
			sendGoalsRequest(e.textEditor,selec.active);
		});

		//Register commands	
		context.subscriptions.push(
			commands.registerCommand('getGoals.start', () => {		
		}));

	});

}

//restart the webview panel
function restartPanel(){
	panel.webview.html = getWebviewContent([]);
}

//returns the HTML code of goals environment
function getGoalsEnvContent(goals : Goal[]){

	let codeHyps : String = ""; //hypothesis HTML code
	let codeGoals : String = ""; //goals HTML code
	let codeEnvGoals : String = ""; //result code HTML

	for(let i=0; i < goals.length; i++){

		codeHyps = `<div class="hypothesis">`;
		codeGoals = `<div class="pp_goals">`;
		for(let j=0; j<goals[i].hyps.length; j++){
			let hnameCode = `<label class="hname">` 
							+ goals[i].hyps[j].hname 
							+ `</label>`; 
			let htypeCode = `<span class="htype">` 
							+ goals[i].hyps[j].htype
							+ `</span> <br/>`;
			codeHyps = codeHyps + hnameCode
						+ `<label class="sep"> : </label>`
						+ htypeCode;
		}
		let numGoalcode = `<label class="numGoal">` 
						+ i + `</label>`;
		let typeGoal = `<span class="goal">` 
						+ goals[i].type + `</span>`;
		codeGoals = codeGoals + numGoalcode 
					+ `<label class ="sep"> : { </label> `
					+ typeGoal + `<label class ="sep">}</label><br/><br/></div>`;

		codeHyps = codeHyps + `</div>`;
		let codeSep = `<hr/>`;
		codeEnvGoals = codeEnvGoals + "" + codeHyps + codeSep + codeGoals;
	} 
	//if there is no goals
	if(goals.length == 0){
		codeEnvGoals = codeEnvGoals + `No goals`;
	} 
	return codeEnvGoals;
}

//returns the HTML code of the panel and the inset ccontent
function getWebviewContent(goals : Goal[]) {
	 
	let htmlPage1 : String;
	let htmlPage2 : String;
	//get the HTML code of goals environment 
	let codeEnvGoals : String = getGoalsEnvContent(goals);
	// #FA8072
	htmlPage1 =  `<!DOCTYPE html>
	<html lang="en">
	<head>
		<meta charset="UTF-8">
		<link rel="stylesheet" type="text/css" href="style/style.css" >
		<meta name="viewport" content="width=device-width, initial-scale=1.0">
		<style>
			.hname{
				color : #F08080;
			}
			.htype {
				color : #FFFFF0;
			}
			.numGoal{
				color : #90EE90; 
			}
			.goal {
				color : #FFEFD5;
			}
			.sep, hr {
				color : #DAA520;	
			}
		</style>
		<title> Goals</title>
	</head>
	<body>
		<p class="goals_env"> ` + codeEnvGoals; 

	htmlPage2 =	` </p>
	</body>
	</html>`;

	return htmlPage1+""+htmlPage2;
}

export interface TextDocumentIdent{
	uri : String // uri of the document
}	

export interface ParamsGoals {
	textDocument : TextDocumentIdent // the current text document
	position : Position // the cursor's position
}

export interface Env {
	hname : String // hypothesis name
	htype : String // hypothesis type
}

export interface Goal {
	gid :  number // goal id
	hyps : Env[] // hypothesis
	type : String // goals
}

export interface GoalResp {
	goals : Goal[]
}

//dispose the previous inset
function clearPreviousInset(){
	if(disposables.length > 0) {
		let x = disposables.pop();
		if(x) x.dispose();
	}
}

//returns the goals at a given cursor's position
function sendGoalsRequest(editor : TextEditor, position: Position) {
	
	let uri = editor.document.uri;
	let doc = {uri : uri.toString()}
	let cursor = {textDocument : doc, position : position}; 
	const req = new RequestType<ParamsGoals, GoalResp, void, void>("proof/goals");
	
	//Send proof/goals request to the server 
	client.sendRequest(req, cursor).then((goals) => {
		if(goals) {
			//return goals;
			let result = getWebviewContent(goals.goals);
			
			//adapt the inset height with goals lines
			let line = position.line;
			let height = result.split('<br/>').length+1;
			//dispose the previous insets
			clearPreviousInset();

			//create new inset
			let inset = window.createWebviewTextEditorInset(editor, line, height);
			disposables.push(inset);

			//update the contents of the panel and the inset
			inset.webview.html = result;
			panel.webview.html = result;

		} else {
			//dispose the previous inset and update the panel's content
			clearPreviousInset();
			panel.webview.html = getWebviewContent([]);
		}
		
	}, _ => {
		panel.webview.html = getWebviewContent([]);
	}); 
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
