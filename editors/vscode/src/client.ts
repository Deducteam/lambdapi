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

                refresh(panel, e, proofState);
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

    const newProofState : Position = stepProofState(context, step); //Proof goes one step earlier
    refresh(panel, openEditor, newProofState); //Goals panel is refreshed

    highlight(context, newProofState, openEditor);
}

function nextProofPosition(document: TextDocument, proofState : Position, direction : number) : Position {

    let current : number = proofState.line + direction; //Starting point

    //The highlight can't go beyond the limits of the document
    if( current == 0 || current == document.lineCount )
        return proofState;

    //Looking for the next line with "proof" in it (or the beggining/end of file)
    let line : string = document.lineAt(current).text;

    while(!line.includes("proof") && current + direction >= 1 && current + direction <= document.lineCount - 1) {
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
    
    refresh(panel, openEditor, nextProofPos); //Goals panel is refreshed

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
    const step : number = proofState.line == documentTotalLines ? 0 : 1;

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
    const step : number = proofState.line == 1 ? 0 : -1;

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
    
    refresh(panel, openEditor, cursorPosition); //Goals panel is refreshed

    highlight(context, cursorPosition, openEditor);
}

function refresh(panel : WebviewPanel, editor : TextEditor | undefined, proofState : Position) {

    if(!editor)
        return;
    
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
