/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import { workspace, ExtensionContext, Position, Uri, commands, window, WebviewPanel, ViewColumn, TextEditor, TextDocument, SnippetString, Range as rg } from 'vscode';

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
} from 'vscode-languageclient';

let client: LanguageClient;

let proofState : Position = new Position(0, 0); //Cursor position when cursor mode is on (see l.65)
let cursorMode : boolean = false; //(see l.65)

let range : rg = new rg(proofState, proofState.translate(1, 0));

const decorationType = window.createTextEditorDecorationType({
    light: {
        backgroundColor: '#CCFFCC',
        border: '1px solid black'
    },
    dark: {
        backgroundColor: '#084035',
        border: '1px solid white'
    }
  });

export function activate(context: ExtensionContext) {

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

        client.onReady().then(() => {

            // Create and show panel
            const panel = window.createWebviewPanel(
                'goals',
                'Goals',
                ViewColumn.Two,
                {}
            );

            window.onDidChangeActiveTextEditor(e => refresh(panel, e, cursorMode));
            window.onDidChangeTextEditorSelection(e => refresh(panel, e.textEditor, cursorMode));

            /*Toggle cursor mode (defaults to false)
                *if true, the "Proof" panel is updated when the cursor is moved
                *if false, updated when "alt+up/down" is pressed
            */
            commands.registerCommand('extension.vscode-lp.cursor', () => {cursorMode = !cursorMode})

            //Step forward in a proof (when cursor mode is off)
            commands.registerCommand('extension.vscode-lp.fw', () => {
                if(!cursorMode){

                    proofState = proofState.translate(1, 0);
                    console.log(proofState.line, cursorMode);
                    refresh(panel, window.activeTextEditor, cursorMode);

                    range = new rg(range.start, proofState.translate(1,0));
                    let openEditor = window.activeTextEditor;

                    if(openEditor != undefined)
                        openEditor.setDecorations(decorationType, [range]);
                }
            })
            
            //Step backwards in a proof (when cursor mode is off)
            commands.registerCommand('extension.vscode-lp.bw', () => {

                if(!cursorMode){
                    let step : number = proofState.line == 0 ? 0 : -1;
                    proofState = proofState.translate(step, 0);
                    console.log(proofState.line);
                    refresh(panel, window.activeTextEditor, cursorMode);
                }

                range = new rg(range.start, proofState.translate(1,0));
                let openEditor = window.activeTextEditor;

                if(openEditor != undefined)
                    openEditor.setDecorations(decorationType, [range]);
            })


        });
        context.subscriptions.push(client.start());
    };

    commands.registerCommand('extension.vscode-lp.restart', restart);
    commands.executeCommand('extension.vscode-lp.fw');
    commands.executeCommand('extension.vscode-lp.bw');
    
    restart();

}

function refresh(panel : WebviewPanel, editor : TextEditor | undefined, cursorMode : boolean) {

    if(editor && cursorMode)
        sendGoalsRequest(editor.selection.active, panel, editor.document.uri);
    
    else if(editor && !cursorMode)
        sendGoalsRequest(proofState, panel, editor.document.uri);


}

// returns the HTML code of goals environment
function getGoalsEnvContent(goals : Goal[]){

    let codeHyps : String = ""; //hypothesis HTML code
    let codeGoals : String = ""; //goals HTML code
    let codeEnvGoals : String = ""; //result code HTML

    for(let i=0; i < goals.length; i++) {

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
            + `<label class ="sep"> : </label> `
            + typeGoal + `<label class ="sep"></label><br/><br/></div>`;

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

// Returns the HTML code of the panel and the inset ccontent
function buildGoalsContent(goals : Goal[]) {
    
    let header, footer : String;

    // get the HTML code of goals environment
    let codeEnvGoals : String = getGoalsEnvContent(goals);

    // Use #FA8072 color too?

    // Note that the style.css file is missing as we don't know yet
    // where it should be placed; this is a TODO.
    header =  `<!DOCTYPE html>
￼       <html lang="en">
￼       <head>
￼               <meta charset="UTF-8">
￼               <link rel="stylesheet" type="text/css" href="style/style.css" >
￼               <meta name="viewport" content="width=device-width, initial-scale=1.0">
￼               <style>
￼                       .hname{
￼                               color : #F08080;
￼                       }
￼                       .htype {
￼                               color : #FFFFF0;
￼                       }
￼                       .numGoal{
￼                               color : #90EE90;
￼                       }
￼                       .goal {
￼                               color : #FFEFD5;
￼                       }
￼                       .sep, hr {
￼                               color : #DAA520;
￼                       }
￼               </style>
￼               <title> Goals</title>
￼       </head>
￼       <body>
￼               <p class="goals_env"> `;
    
    footer =` </p>
￼       </body>
￼       </html>`;
    
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
	gid :  number // goal id
	hyps : Env[] // hypothesis
	type : String // goals
}

export interface GoalResp {
    goals : Goal[]
}

function sendGoalsRequest(position: Position, panel : WebviewPanel, uri : Uri) {

    let doc = {uri : uri.toString()}
    let cursor = {textDocument : doc, position : position};
    const req = new RequestType<ParamsGoals, GoalResp, void, void>("proof/goals");
    client.sendRequest(req, cursor).then((goals) => {
        if(goals) {
            let goal_render = buildGoalsContent(goals.goals);
            panel.webview.html = goal_render
            // Disabled as this is experimental
	    // let wb = window.createWebviewTextEditorInset(window.activeTextEditor, line, height);
	    // wb.webview.html = panel.webview.html;
        } else {
            panel.webview.html = buildGoalsContent([]);
        }
    }, () => { panel.webview.html = buildGoalsContent([]); });
}

export function deactivate(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    }
    return client.stop();
}
