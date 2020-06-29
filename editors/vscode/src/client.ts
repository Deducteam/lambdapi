/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import { workspace, ExtensionContext, Position, Uri, commands, window, WebviewPanel, ViewColumn, TextEditor, TextDocument, SnippetString, Range as rg, TextEditorDecorationType } from 'vscode';

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

    //___Declaration of workspace variables___

    //Position of the proof cursor : colored highlights show until which point the proof was surveyed
    let proofState : Position = new Position(1, 0);
    context.workspaceState.update('proofState', proofState);

    //Cursor mode (proof cursor is the regular cursor) activated or not
    context.workspaceState.update('cursorMode', false);

    //The range of text to highlight
    let range : rg = new rg(proofState.translate(-1, 0), proofState);
    context.workspaceState.update('range', range);

    //The highlight parameters
    const proofDecoration = window.createTextEditorDecorationType({
        light: {
            backgroundColor: '#CCFFCC' //highlight color for a light theme
        },
        dark: {
            backgroundColor: '#084035' //highlight color for a dark theme
        }
      });
    context.workspaceState.update('proofDecoration', proofDecoration);

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

        client.onReady().then(async () => {

            // Create and show panel for proof goals
            const panel = window.createWebviewPanel(
                'goals',
                'Goals',
                ViewColumn.Two,
                {}
            );

            window.onDidChangeActiveTextEditor(e => {
                const proofState : Position = context.workspaceState.get('proofState') ?? new Position(0, 0);
                const cursorMode : boolean = context.workspaceState.get('cursorMode') ?? false;
                refresh(panel, e, proofState);
            });

            window.onDidChangeTextEditorSelection(e => { 
                const proofState : Position = context.workspaceState.get('proofState') ?? new Position(0, 0);
                const cursorMode : boolean = context.workspaceState.get('cursorMode') ?? false;

                if(!cursorMode)
                    return;

                checkProofUntilCursor(context, panel, proofState);
            });

            /*Toggle cursor mode (defaults to false)
                *if true, the "Proof" panel is updated when the cursor is moved
                *if false, updated when keybindings are pressed
            */
            commands.registerCommand('extension.vscode-lp.cursor', () => toggleCursorMode(context));
 
            //Navigate proof : step forward in a proof (when cursor mode is off)
            commands.registerCommand('extension.vscode-lp.fw', () => {

                const cursorMode : boolean = context.workspaceState.get('cursorMode') ?? false;
                if(cursorMode)
                    return;

                const proofState : Position = context.workspaceState.get('proofState') ?? new Position(0, 0);
                checkProofForward(context, panel, proofState);
            });
            
            //Navigate proof : step backwards in a proof (when cursor mode is off)
            commands.registerCommand('extension.vscode-lp.bw', () => {

                const cursorMode : boolean = context.workspaceState.get('cursorMode') ?? false;
                if(cursorMode)
                    return;
                
                const proofState : Position = context.workspaceState.get('proofState') ?? new Position(0, 0);
                checkProofBackwards(context, panel, proofState);
            });

            //Navigate proof : move proof higlight to cursor (when cursor mode is off)
            commands.registerCommand('extension.vscode-lp.tc', () => {

                const cursorMode : boolean = context.workspaceState.get('cursorMode') ?? false;
                if(cursorMode)
                    return;
                
                const proofState : Position = context.workspaceState.get('proofState') ?? new Position(0, 0);
                checkProofUntilCursor(context, panel, proofState);
            });

            //Highlight first line
            if(window.activeTextEditor)
                decorate(window.activeTextEditor, range, proofDecoration);
        });

        context.subscriptions.push(client.start());
    };
    
    commands.registerCommand('extension.vscode-lp.restart', restart);
    
    restart();
}

function toggleCursorMode(context : ExtensionContext) : boolean {
    let cursorMode : boolean = context.workspaceState.get('cursorMode') ?? false;

    cursorMode = !cursorMode;
    context.workspaceState.update('cursorMode', cursorMode);

    return cursorMode;
}

function decorate(openEditor : TextEditor, range : rg, decorationType : TextEditorDecorationType) {
    if(openEditor != undefined)
        openEditor.setDecorations(decorationType, [range]);
}

function updateHighlightRange(context : ExtensionContext, proofState : Position, offset : number) : rg {
    

    let range : rg = context.workspaceState.get('range') ?? new rg(new Position(0, 0), proofState);
    
    let rangeEnd : Position = new Position(proofState.line + 1, 0);

    

    range = new rg(range.start, rangeEnd);
    context.workspaceState.update('range', range);

    return range;
}

function stepProofState(context : ExtensionContext, step : number) {

    let proofState : Position = context.workspaceState.get('proofState') ?? new Position(0, 0);

    proofState = proofState.translate(step, 0);
    context.workspaceState.update('proofState', proofState);

    

    return proofState;

}

function checkProofForward(context : ExtensionContext, panel : WebviewPanel, proofState : Position) {

    const openEditor : TextEditor | undefined = window.activeTextEditor;
    if(!openEditor)
        return;

    const documentTotalLines : number = openEditor.document.lineCount ?? 0;
    const step : number = proofState.line == documentTotalLines ? 0 : 1;

    if(step) {

        const newProofState : Position = stepProofState(context, step);
        
        refresh(panel, openEditor, newProofState);

        const range : rg = updateHighlightRange(context, newProofState, 1);
        const proofDecoration : TextEditorDecorationType = context.workspaceState.get('proofDecoration') ?? window.createTextEditorDecorationType({});

        decorate(openEditor, range, proofDecoration);
    }
}

function checkProofBackwards(context : ExtensionContext, panel : WebviewPanel, proofState : Position) {

    const openEditor : TextEditor | undefined = window.activeTextEditor;
    if(!openEditor)
        return;

    const step : number = proofState.line == 1 ? 0 : -1;

    if(step == -1) {
        
        const newProofState : Position = stepProofState(context, step);
        refresh(panel, openEditor, newProofState);

        const range : rg = updateHighlightRange(context, newProofState, 0);
        const proofDecoration : TextEditorDecorationType = context.workspaceState.get('proofDecoration') ?? window.createTextEditorDecorationType({});

        decorate(openEditor, range, proofDecoration);
    }
}

function checkProofUntilCursor(context : ExtensionContext, panel : WebviewPanel, proofState : Position) {

    const openEditor : TextEditor | undefined = window.activeTextEditor;
    if(!openEditor)
        return;
    
    let cursorPosition : Position =  openEditor.selection.active;    
    if (proofState.line == cursorPosition.line) 
        return;
    
    if (cursorPosition.character != 0)
        cursorPosition = new Position(cursorPosition.line, 0);
    
    context.workspaceState.update('proofState', cursorPosition);
    
    refresh(panel, openEditor, cursorPosition);

    const range : rg = updateHighlightRange(context, cursorPosition, -1);
    const proofDecoration : TextEditorDecorationType = context.workspaceState.get('proofDecoration') ?? window.createTextEditorDecorationType({});

    decorate(openEditor, range, proofDecoration);
}

function refresh(panel : WebviewPanel, editor : TextEditor | undefined, proofState : Position) {

    if(!editor)
        return;
    
    sendGoalsRequest(editor.selection.active, panel, editor.document.uri);
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
