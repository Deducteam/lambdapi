/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import { workspace, ExtensionContext, Position, Uri, commands, window, WebviewPanel, ViewColumn, TextEditor, TextDocument, SnippetString, Range as rg, TextEditorDecorationType, Pseudoterminal, EventEmitter, TreeItemCollapsibleState, WebviewViewProvider, CancellationToken, WebviewView, WebviewViewResolveContext } from 'vscode';

// Insiders API, disabled
// import { WebviewEditorInset } from 'vscode';

import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    TransportKind,
    RequestType,
    NotificationType,
    TextDocumentIdentifier,
    RegistrationRequest,
    DocumentSymbolRequest,
} from 'vscode-languageclient';

import { time } from 'console';

let client: LanguageClient;

export function activate(context: ExtensionContext) {

    const provider = new DebugViewProvider(context.extensionUri);
    context.subscriptions.push(window.registerWebviewViewProvider('lambdapi.debugView', provider));

    //___Declaration of workspace variables___

    //Position of the proof cursor : colored highlights show until which point the proof was surveyed
    let proofState : Position = new Position(0, 0);
    context.workspaceState.update('proofState', proofState);

    //Cursor mode (proof cursor is the regular cursor) activated or not
    context.workspaceState.update('cursorMode', false);

    //The range of text to highlight
    let range : rg = new rg(proofState, proofState.translate(1,0));
    context.workspaceState.update('range', range);

    //The highlight parameters
    const proofDecoration = window.createTextEditorDecorationType({
        light: {
            backgroundColor: '#33CC3355' //highlight color for a light theme
        },
        dark: {
            backgroundColor: '#08883555' //highlight color for a dark theme
        }
      });
    context.workspaceState.update('proofDecoration', proofDecoration);

    //Following mode : whether the window follows proofState automatically or not
    context.workspaceState.update('follow', true);

    // XXX: Get from configuration
    let serverOptions = {
        command: 'lambdapi',
        args: [ 'lsp' ]
        // args: [ '--std' ]
    };

    let clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'lp' }],
    };

    const restart = () => {

        if (client) {
            client.stop();
        }

        client = new LanguageClient(
            'LambdaPi-VSCode',
            'Lambdapi Language Server',
            serverOptions,
            clientOptions
        );

        client.onReady().then( () => {

            // Create and show panel for proof goals
            const panel = window.createWebviewPanel(
                'goals',
                'Goals',
                ViewColumn.Two,
                {}
            );
            context.workspaceState.update('panel', panel);

            window.onDidChangeActiveTextEditor(e => {

                const proofState : Position | undefined = context.workspaceState.get('proofState');
                const panel : WebviewPanel | undefined = context.workspaceState.get('panel');

                if (!proofState || !panel) {
                    console.log('onDidChangeActiveTextEditor : workspace variables are not properly defined');
                    return;
                }

                refresh(panel, e, proofState, context);
            });

            window.onDidChangeTextEditorSelection(e => { 

                const cursorMode : boolean = context.workspaceState.get('cursorMode') ?? false;
                if(!cursorMode)
                    return;

                checkProofUntilCursor(context);
            });

            /*Toggle cursor mode (defaults to false)
                *if true, the "Proof" panel is updated when the cursor is moved
                *if false, updated when keybindings are pressed
            */
            commands.registerCommand('extension.vscode-lp.cursor', () => toggleCursorMode(context));
 
            //Navigate proof : step forward in a proof 
            commands.registerCommand('extension.vscode-lp.fw', () => checkProofForward(context));
            
            //Navigate proof : step backward in a proof
            commands.registerCommand('extension.vscode-lp.bw', () => checkProofBackward(context));

            //Navigate proof : move proof higlight to cursor
            commands.registerCommand('extension.vscode-lp.tc', () => checkProofUntilCursor(context));
            
            //Window follows proof or not
            commands.registerCommand('extension.vscode-lp.reveal', () => toggleFollowMode(context))

            //Center window on proof state
            commands.registerCommand('extension.vscode-lp.center', () => goToProofState(context));

            //Go to next/previous proof
            commands.registerCommand('extension.vscode-lp.nx', () => nextProof(context, 1));
            commands.registerCommand('extension.vscode-lp.pv', () => nextProof(context, -1));


            //Highlight first line
            if(window.activeTextEditor)
                decorate(window.activeTextEditor, range, proofDecoration);
        });

        context.subscriptions.push(client.start());
    };
    
    commands.registerCommand('extension.vscode-lp.restart', restart);
    
    restart();
}

function highlight(context : ExtensionContext, newProofState : Position, openEditor : TextEditor) {

    const range : rg = updateHighlightRange(context, newProofState); //Highlight range is updated

    //Highlighting text
    const proofDecoration : TextEditorDecorationType | undefined = context.workspaceState.get('proofDecoration');

    if(!proofDecoration)
        console.log('Highlights/decorations are not properly defined');
    else
        decorate(openEditor, range, proofDecoration);
    
    //Scroll until last highlight (if follow mode is toggled)
    const follow: boolean | undefined = context.workspaceState.get('follow');

    if(follow)
        commands.executeCommand('revealLine', {lineNumber: newProofState.line, at: 'center'});
}

function lpRefresh(context : ExtensionContext, step : number, panel : WebviewPanel, openEditor : TextEditor) {

    const newProofState : Position = stepProofState(context, step); //Proof goes one step further/earlier
    refresh(panel, openEditor, newProofState, context); //Goals panel is refreshed

    highlight(context, newProofState, openEditor);
}

function nextProofPosition(document: TextDocument, proofState : Position, direction : number) : Position {

    let current : number = proofState.line + direction; //Starting point

    //The highlight can't go beyond the limits of the document
    if( current <= 0 || current >= document.lineCount )
        return proofState;

    //Looking for the next line with "proof" in it (or the beggining/end of file)
    let line : string = document.lineAt(current).text;

    while(!line.includes("begin") && current + direction >= 1 && current + direction <= document.lineCount - 1) {
        current += direction;
        line = document.lineAt(current).text;
    }

    return new Position(current, 0);
}


function nextProof(context : ExtensionContext, direction : number) {

    //Checking workspace
    const openEditor : TextEditor | undefined = window.activeTextEditor;
    if(!openEditor) {
        console.log("No editor opened");
        return;
    }
    
    const proofState : Position | undefined = context.workspaceState.get('proofState');
    const panel : WebviewPanel | undefined = context.workspaceState.get('panel');

    if (!proofState || !panel) {
        console.log('nextProof : workspace variables are not properly defined');
        return;
    }

    //The position of the next proof
    let nextProofPos : Position = nextProofPosition(openEditor.document, proofState, direction);
    
    context.workspaceState.update('proofState', nextProofPos); //proof state is set to the position of the next proof keyword
    
    refresh(panel, openEditor, nextProofPos, context); //Goals panel is refreshed

    highlight(context, nextProofPos, openEditor);
}

function goToProofState(context : ExtensionContext){
    
    const proofState : Position | undefined = context.workspaceState.get('proofState');
    if(!proofState) {
        console.log("goToProofState : proofState workspace variable not set properly");
        return;
    }

    commands.executeCommand('revealLine', {lineNumber: proofState.line, at: 'center'});
}

function toggleCursorMode(context : ExtensionContext) : boolean {
    let cursorMode : boolean = context.workspaceState.get('cursorMode') ?? false;

    cursorMode = !cursorMode;
    context.workspaceState.update('cursorMode', cursorMode);

    if(cursorMode) {
        
        window.showInformationMessage("Cursor navigation enabled");

        //By default, follow mode is disabled in cursor mode (because it may be nausea-inducing)
        if( context.workspaceState.get('follow') )
            toggleFollowMode(context);
    }
    
    else {

        window.showInformationMessage("Cursor navigation disabled");

        //By default, follow mode is enabled when cursor mode is off (because it is more practical)
        if( !context.workspaceState.get('follow') )
            toggleFollowMode(context);
    }
    
    return cursorMode;
}

function toggleFollowMode(context : ExtensionContext) : boolean {
    let follow : boolean = context.workspaceState.get('follow') ?? false;

    follow = !follow;
    context.workspaceState.update('follow', follow);


    if(follow)
        window.showInformationMessage("Window follows highlights");
    
    else
        window.showInformationMessage("Window doesn't follow highlights");

    return follow;
}

function decorate(openEditor : TextEditor, range : rg, decorationType : TextEditorDecorationType) {
    openEditor.setDecorations(decorationType, [range]);
}

function updateHighlightRange(context : ExtensionContext, proofState : Position) : rg {
    
    let range : rg = context.workspaceState.get('range') ?? new rg(new Position(0, 0), proofState);
    let rangeEnd : Position = new Position(proofState.line + 1, 0);

    range = new rg(range.start, rangeEnd);
    context.workspaceState.update('range', range);

    return range;
}

function stepProofState(context : ExtensionContext, step : number) {

    let proofState : Position | undefined = context.workspaceState.get('proofState');

    if(!proofState) {
        console.log('stepProofState : proofState workspace variable is not properly defined');
        proofState = new Position(1, 0);
        context.workspaceState.update('proofState', proofState);
        return proofState;
    }

    proofState = proofState.translate(step, 0);
    context.workspaceState.update('proofState', proofState);

    return proofState;
}

function checkProofForward(context : ExtensionContext) {

    //Checking workspace
    const openEditor : TextEditor | undefined = window.activeTextEditor;
    if(!openEditor)
        return;
    
    const proofState : Position | undefined = context.workspaceState.get('proofState');
    const panel : WebviewPanel | undefined = context.workspaceState.get('panel');
    if (!proofState || !panel) {
        console.log('checkProofForward : Workspace variables are not properly defined');
        return;
    }

    //If the proof highlight is at the end of the document it can't go further
    const documentTotalLines : number = openEditor.document.lineCount ?? 0;
    const step : number = proofState.line >= documentTotalLines ? 0 : 1;

    //Case the end has not been reached
    if(step)
        lpRefresh(context, step, panel, openEditor);
}

function checkProofBackward(context : ExtensionContext) {

    //Checking workspace
    const openEditor : TextEditor | undefined = window.activeTextEditor;
    if(!openEditor)
        return;

    const proofState : Position | undefined = context.workspaceState.get('proofState');
    const panel : WebviewPanel | undefined = context.workspaceState.get('panel');
    if (!proofState || !panel) {
        console.log('checkProofBackward : Workspace variables are not properly defined');
        return;
    }

    //If the proof highlight is at the beggining of the document it can't go any higher
    const step : number = proofState.line <= 0 ? 0 : -1;

    //Case the proof state is not at the beggining of the document
    if(step == -1)
        lpRefresh(context, step, panel, openEditor);
}

function checkProofUntilCursor(context : ExtensionContext) {

    //Checking workspace
    const openEditor : TextEditor | undefined = window.activeTextEditor;
    if(!openEditor)
        return;
    
    const proofState : Position | undefined = context.workspaceState.get('proofState');
    const panel : WebviewPanel | undefined = context.workspaceState.get('panel');

    if (!proofState || !panel) {
        console.log('checkProofUntilCursor : workspace variables are not properly defined');
        return;
    }
    
    //The current position of the cursor
    let cursorPosition : Position =  openEditor.selection.active;    
    if (proofState.line == cursorPosition.line) 
        return;
    
    //To simplify the code, proof states are always at the beggining of the highlighted line
    //So must be the cursor position since it is the new proof state
    if (cursorPosition.character != 0)
        cursorPosition = new Position(cursorPosition.line, 0);
    
    context.workspaceState.update('proofState', cursorPosition); //proof state is set to the cursor position
    
    refresh(panel, openEditor, cursorPosition, context); //Goals panel is refreshed

    highlight(context, cursorPosition, openEditor);
}

function refresh(panel : WebviewPanel, editor : TextEditor | undefined, proofState : Position, context : ExtensionContext) {

    if(!editor)
        return;
    
    const styleUri = panel.webview.asWebviewUri(Uri.joinPath(context.extensionUri, 'media', 'styles.css'))
    sendGoalsRequest(proofState, panel, editor.document.uri, styleUri);
}

// returns the HTML code of goals environment
function getGoalsEnvContent(goals : Goal[]){

    let codeHyps : String = ""; //hypothesis HTML code
    let codeGoals : String = ""; //goals HTML code
    let codeEnvGoals : String = ""; //result code HTML

    for(let i=0; i < goals.length; i++) {
        
        codeHyps = `<div class="hypothesis">`;
        codeGoals = `<div class="pp_goals">`;
        
        // check if this is a Type Goal
    	// extra space is not a typo, this is defined in lsp_base.ml
        if (goals[i].typeofgoal == "Typ "){

            let curGoal = goals[i] as TypGoal;

            for(let j=0; j<curGoal.hyps.length; j++){

                let hnameCode = `<label class="hname">`
                    + curGoal.hyps[j].hname
                    + `</label>`;

                let htypeCode = `<span class="htype">`
                    + curGoal.hyps[j].htype
                + `</span> <br/>`;

                codeHyps = codeHyps + hnameCode
                    + `<label class="sep"> : </label>`
                    + htypeCode;
            }
        }

        let numGoalcode = `<label class="numGoal">`
            + i + `</label>`;

        let goalstr = "";
        if(goals[i].typeofgoal == "Typ "){
            goalstr = `<span class="goal">`
                + (goals[i] as TypGoal).type + `</span>`;
        } else {
            goalstr = `<span class="goal">`
                + (goals[i] as UnifGoal).constr + `</span>`;
        }

        codeGoals += numGoalcode + `<label class ="sep"> : </label> `
                    + goalstr + `<label class ="sep"></label><br/><br/></div>`;

        codeHyps = codeHyps + `</div>`;

        let codeSep = `<hr/>`;
        codeEnvGoals = codeEnvGoals + "" + codeHyps + codeSep + codeGoals;

    }

    // if there is no goal
    if(goals.length == 0){
        codeEnvGoals = codeEnvGoals + `No goals`;
    }
    return codeEnvGoals;
}

var termWritable = true;
// to ensure user can't send text to terminal
function updateTerminalText(logstr: string){
    const termName = "Lambdapi Debug";
    const clearTextSeq = '\x1b[2J\x1b[3J\x1b[;H';

    let term = window.terminals.find((t) => t.name == termName);
    console.log("Term=");
    console.log(term);
    if(!term){
        const writeEmitter = new EventEmitter<string>();
        const pty : Pseudoterminal = {
            onDidWrite: writeEmitter.event,
            open: () => {},
            close: () => {},
            handleInput: (data: string) => {
                data = data.replace(/\r/g, '\r\n');
                console.log(`TermWritable=${termWritable}`)
                console.log("data=" + JSON.stringify(data)+"\n\n");
                if(termWritable || true){
                    writeEmitter.fire(data)
                    termWritable = false;
                }
            }
        };
        term = window.createTerminal({name: termName, pty});
        term.show(true);
    }

    term.sendText(clearTextSeq);
    term.sendText(logstr);
}

// Returns the HTML code of the panel and the inset ccontent
function buildGoalsContent(goals : Goal[], styleUri : Uri) {
    
    let header, footer : String;

    // get the HTML code of goals environment
    let codeEnvGoals : String = getGoalsEnvContent(goals);

    // Use #FA8072 color too?

    // Note that the style.css file is missing as we don't know yet
    // where it should be placed; this is a TODO.
    // NOTE: multiline strings will introduce character sequences
    //       which WebviewPanel can't display
    header =  `<!DOCTYPE html>
￼       <html lang="en">
￼       <head>
￼               <meta charset="UTF-8">
￼               <link rel="stylesheet" type="text/css" href="${styleUri}" >
￼               <meta name="viewport" content="width=device-width, initial-scale=1.0">
￼               <title> Goals</title>
￼       </head>
￼       <body>
￼               <p class="goals_env"> `;
    
    footer =` </p>
￼       </body>
￼       </html>`;

    // remove character sequences caused by multiline strings
    header = header.replace(/[\u{0080}-\u{FFFF}]/gu,"");
    footer = footer.replace(/[\u{0080}-\u{FFFF}]/gu,"");
    
    return header + codeEnvGoals + footer;
}

export interface TextDocumentIdent{
    uri : String
}

export interface ParamsGoals {
    textDocument : TextDocumentIdent // current text document
    position : Position         // position to get goals
}

export interface Env {
	hname : String // hypothesis name
	htype : String // hypothesis type
}

export interface Goal {
    typeofgoal : String // type of goal, values defined in lsp_base.ml
}

export interface UnifGoal extends Goal {
    constr : String
}

export interface TypGoal extends Goal {
	gid :  number // goal id
	hyps : Env[] // hypothesis
	type : String // goals
}

export interface GoalResp {
    goals : Goal[]
    logs : string
}

function sendGoalsRequest(position: Position, panel : WebviewPanel, docUri : Uri, styleUri : Uri) {

    let doc = {uri : docUri.toString()}
    let cursor = {textDocument : doc, position : position};
    const req = new RequestType<ParamsGoals, GoalResp, void, void>("proof/goals");
    client.sendRequest(req, cursor).then((goals) => {
        
        if(goals.logs){
            updateTerminalText(goals.logs);
        }

        if(goals.goals) {
            let goal_render = buildGoalsContent(goals.goals, styleUri);
            panel.webview.html = goal_render
            // Disabled as this is experimental
	    // let wb = window.createWebviewTextEditorInset(window.activeTextEditor, line, height);
	    // wb.webview.html = panel.webview.html;
        } else {
            panel.webview.html = buildGoalsContent([], styleUri);
        }
    }, () => { panel.webview.html = buildGoalsContent([], styleUri); });
}


export function deactivate(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    }
    return client.stop();
}



import * as vscode from 'vscode';

class DebugViewProvider implements vscode.WebviewViewProvider {
	public static readonly viewType = 'lambdapi.debugView';

	private _view?: vscode.WebviewView;

	constructor(
		private readonly _extensionUri: vscode.Uri,
	) { }
	resolveWebviewView(webviewView: vscode.WebviewView, context: vscode.WebviewViewResolveContext<unknown>, _token: vscode.CancellationToken): void | Thenable<void> {
		this._view = webviewView;

		webviewView.webview.options = {
			// Allow scripts in the webview
			enableScripts: true,

			localResourceRoots: [
				this._extensionUri
			]
		};

		webviewView.webview.html = this._getHtmlForWebview();

		webviewView.webview.onDidReceiveMessage(data => {
            console.log("Recieved" + JSON.stringify(data) + "\n\n");
			switch (data.type) {
				case 'debug':
					{
                        let params = {'flags': data.flags};
                        client.sendNotification('proof/debugFlags', params);
                        console.log(`sent : ${JSON.stringify(params)}\n`);
					}
			}
		});
	}

	private _getHtmlForWebview(){
        // TODO use external stylesheet
        let html = `<!DOCTYPE html>
        <html lang="en">
        <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <style type="text/css">
                .key {
                    font-weight: bold;
                    text-decoration: underline;
                }
            </style>
        </head>
        <body>
            <input type="checkbox" value="c" onchange="sendFlags()">[c]onversion</input><br>
            <input type="checkbox" value="e" onchange="sendFlags()">[e]valuation</input><br>
            <input type="checkbox" value="f" onchange="sendFlags()">[f]ile system</input><br>
            <input type="checkbox" value="g" onchange="sendFlags()">[g]enerating induction principle</input><br>
            <input type="checkbox" value="h" onchange="sendFlags()">command [h]andling</input><br>
            <input type="checkbox" value="i" onchange="sendFlags()">[i]nference/checking</input><br>
            <input type="checkbox" value="p" onchange="sendFlags()">[p]retty-printing</input><br>
            <input type="checkbox" value="r" onchange="sendFlags()">[r]ewrite tactic</input><br>
            <input type="checkbox" value="s" onchange="sendFlags()">[s]ubject reduction</input><br>
            <input type="checkbox" value="t" onchange="sendFlags()">[t]actic</input><br>
            <input type="checkbox" value="u" onchange="sendFlags()">[u]nification</input><br>
            <input type="checkbox" value="w" onchange="sendFlags()">[w]hy3 prover</input><br>
            <input type="checkbox" value="x" onchange="sendFlags()">e[x]ternal tools</input><br>

            <script>
                const vscode = acquireVsCodeApi();
                function sendFlags(){
                    const checkboxes = document.querySelectorAll('input:checked')
                    let flags = "";
                    checkboxes.forEach((cb) => {flags += cb.value});
                    vscode.postMessage({
                        'type': 'debug',
                        'flags': flags
                    });
                }
            </script>
        </body>
        </html>`;
        // replace [x]
        html = html.replace(/\[(.)\]/g, '<span class="key">$1</span>');
        return html;
     }
	
}
