// VSCode extension for https://github.com/Deducteam/lambdapi
// a proof assistant based on the λΠ-calculus modulo rewriting

import { workspace, ExtensionContext, Position, Uri, commands, window, WebviewPanel, ViewColumn, TextEditor, TextDocument, SnippetString, Range, TextEditorDecorationType, Pseudoterminal, EventEmitter, TreeItemCollapsibleState, WebviewViewProvider, CancellationToken, WebviewView, WebviewViewResolveContext, TextDocumentChangeEvent, Diagnostic, languages } from 'vscode';

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

import { assert, time } from 'console';

let client: LanguageClient;

export function activate(context: ExtensionContext) {

    workspace.onDidChangeTextDocument((e)=>{
        lpDocChangeHandler(e, context);
    })

    //___Declaration of workspace variables___

    //Position of the proof cursor : colored highlights show until which point the proof was surveyed
    let proofState : Position = new Position(0, 0);
    context.workspaceState.update('proofState', proofState);

    //Cursor mode (proof cursor is the regular cursor) activated or not
    context.workspaceState.update('cursorMode', false);

    //The range of text to highlight
    let range : Range = new Range(new Position(0, 0), proofState);
    context.workspaceState.update('range', range);

    //The highlight parameters
    const proofDecoration = window.createTextEditorDecorationType({
        light: {
            backgroundColor: '#33CC3355' //highlight color for a light theme
        },
        dark: {
            backgroundColor: '#08883555' //highlight color for a dark theme
        },
        rangeBehavior: 1 // ClosedClosed
      });
    const errorDecoration = window.createTextEditorDecorationType({
        light: {
            backgroundColor: '#FF000055' //highlight color for a light theme
        },
        dark: {
            backgroundColor: '#FF000055' //highlight color for a dark theme
        },
        rangeBehavior: 1 // ClosedClosed
      });
    context.workspaceState.update('proofDecoration', proofDecoration);
    context.workspaceState.update('errorDecoration', errorDecoration);

    //Following mode : whether the window follows proofState automatically or not
    context.workspaceState.update('follow', true);
    
    const lspServerPath = workspace.getConfiguration('lambdapi').path;
    console.log(lspServerPath);

    let serverOptions = {
        command: lspServerPath,
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
            'lambdapi',
            'lambdapi language server',
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

                refreshGoals(panel, e, proofState, context);
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
            commands.registerCommand('extension.lambdapi.cursor', () => toggleCursorMode(context));
 
            //Navigate proof : step forward in a proof 
            commands.registerCommand('extension.lambdapi.fw', () => checkProofForward(context));
            
            //Navigate proof : step backward in a proof
            commands.registerCommand('extension.lambdapi.bw', () => checkProofBackward(context));

            //Navigate proof : move proof highlight to cursor
            commands.registerCommand('extension.lambdapi.tc', () => checkProofUntilCursor(context));
            
            //Window follows proof or not
            commands.registerCommand('extension.lambdapi.reveal', () => toggleFollowMode(context))

            //Center window on proof state
            commands.registerCommand('extension.lambdapi.center', () => goToProofState(context));

            //Go to next/previous proof
            commands.registerCommand('extension.lambdapi.nx', () => nextProof(context, true));
            commands.registerCommand('extension.lambdapi.pv', () => nextProof(context, false));

        });

        context.subscriptions.push(client.start());
    };
    
    commands.registerCommand('extension.lambdapi.restart', restart);
    
    restart();
}

function lpDocChangeHandler(event : TextDocumentChangeEvent, context: ExtensionContext) {

    if(event.document != window.activeTextEditor?.document){
        // should not happen
        console.log("Changes not on the active TextEditor");
        return;
    }
    let proofPos : Position | undefined = context.workspaceState.get('proofState');
    if (!proofPos) proofPos = new Position(0, 0);

    let firstChange : Position | undefined = undefined;
    for(let i = 0; i < event.contentChanges.length; i++){
        let change = event.contentChanges[i];
        let changeStart : Position = change.range.start;
        if(firstChange != undefined) 
            firstChange = changeStart.isBefore(firstChange) ? changeStart : firstChange;
        else 
            firstChange = changeStart;
    }

    if(firstChange && firstChange.isBefore(proofPos)){
        // region inside proved region is changed
        // update the proofState
        let newPos = stepCommand(event.document, firstChange, false);

        const panel : WebviewPanel | undefined = context.workspaceState.get('panel');
        if (!panel) {
            console.log('lpDocChangeHandler : workspace variables are not properly defined');
            return;
        }
        context.workspaceState.update('proofState', newPos);
        refreshGoals(panel, window.activeTextEditor, newPos, context);
        highlight(context, newPos, window.activeTextEditor);
    }
}

function getFirstError(uri : Uri, before? : Position){
    let diags : Diagnostic[] = languages.getDiagnostics(uri);
    let firstError : Position | undefined = undefined;
    let ind = 0;
    for (let diag of diags){
        if (diag.severity == 0) {//check if error
            if(firstError){
                firstError = diag.range.start.isBefore(firstError) ? diag.range.start : firstError;
            } else {
                firstError = diag.range.start;
            }
        }
    }
    if(before){
        if(firstError && firstError.isBefore(before)) return firstError;
        else return undefined;
    } else { 
        return firstError;
    }
}

function highlight(context : ExtensionContext, newProofState : Position, openEditor : TextEditor) {


    //Highlighting text
    const proofDecoration : TextEditorDecorationType | undefined = context.workspaceState.get('proofDecoration');
    const errorDecoration : TextEditorDecorationType | undefined = context.workspaceState.get('errorDecoration');

    const firstError = getFirstError(openEditor.document.uri, newProofState);
    const zeroPos = new Position(0, 0);

    if(!proofDecoration || !errorDecoration)
        console.log('Highlights/decorations are not properly defined');
    else{
        if(firstError){
            decorate(openEditor, new Range(zeroPos, firstError), proofDecoration);
            decorate(openEditor, new Range(firstError, newProofState), errorDecoration);
        } else {
            decorate(openEditor, null, errorDecoration);
            decorate(openEditor, new Range(zeroPos, newProofState), proofDecoration);
        }
        
    }
    //Scroll until last highlight (if follow mode is toggled)
    const follow: boolean | undefined = context.workspaceState.get('follow');

    if(follow)
        commands.executeCommand('revealLine', {lineNumber: newProofState.line, at: 'center'});
}

function lpRefresh(context : ExtensionContext, proofPos : Position, panel : WebviewPanel, openEditor : TextEditor) {

    context.workspaceState.update('proofState', proofPos);

    refreshGoals(panel, openEditor, proofPos, context); //Goals panel is refreshed

    highlight(context, proofPos, openEditor);
}

function nextProof(context : ExtensionContext, direction : boolean) {

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
    let nextProofPos : Position = stepCommand(openEditor.document, proofState, direction, ['begin']);
    
    context.workspaceState.update('proofState', nextProofPos); //proof state is set to the position of the next proof keyword
    
    refreshGoals(panel, openEditor, nextProofPos, context); //Goals panel is refreshed

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

function decorate(openEditor : TextEditor, range : Range | null, decorationType : TextEditorDecorationType) {
    if(range)
        openEditor.setDecorations(decorationType, [range]);
    else
        openEditor.setDecorations(decorationType, []);
}

// returns the Position of next or previous command
function stepCommand(document: TextDocument, currentPos: Position, forward: boolean, terminators?: string[]){

    if(terminators === undefined || terminators === null)
        terminators = [';', 'begin', '{'];

    let docBegin : Position = document.positionAt(0);
    let docEnd : Position = new Position(document.lineCount, 0);

    const minPos = (a : Position, b : Position) => a.compareTo(b) < 0 ? a : b;
    const maxPos = (a : Position, b : Position) => a.compareTo(b) > 0 ? a : b;
    const termRegex = new RegExp(terminators.join("|"), 'gi');

    let termPositions = [...document.getText().matchAll(termRegex)]
        .map(rm => rm.index ? rm.index + rm[0].length : undefined)
        .filter((x) : x is number => x !== undefined) // remove undefined
        .map(x => document.positionAt(x));

    let nextCmdPos = termPositions
        .filter(p => currentPos.compareTo(p) * (forward ? 1 : -1) < 0)
        .reduce(forward ? minPos : maxPos, forward ? docEnd : docBegin);

    return nextCmdPos;
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

    let newPos = stepCommand(openEditor.document, proofState, true);
    if(newPos)
        lpRefresh(context, newPos, panel, openEditor);
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

    let newPos = stepCommand(openEditor.document, proofState, false);

    //Case the end has not been reached
    if(newPos)
        lpRefresh(context, newPos, panel, openEditor);
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
    
    refreshGoals(panel, openEditor, cursorPosition, context); //Goals panel is refreshed

    highlight(context, cursorPosition, openEditor);
}

function refreshGoals(panel : WebviewPanel, editor : TextEditor | undefined, proofState : Position, context : ExtensionContext) {

    if(!editor)
        return;
    
    const styleUri = panel.webview.asWebviewUri(Uri.joinPath(context.extensionUri, 'media', 'styles.css'))
    sendGoalsRequest(proofState, panel, editor.document.uri, styleUri);
}

// returns the HTML code of goals environment
function getGoalsEnvContent(goals : Goal[]){

    if(goals.length == 0)
        return "No goals";

    return goals.map((curGoal, itr) => {
        let goalStr = curGoal.typeofgoal == "Typ" ? (curGoal as TypGoal).type : (curGoal as UnifGoal).constr;
        return '<div class="hypothesis">' +
                curGoal.hyps.map((hyp) => {
                    return `<label class="hname">${hyp.hname}</label>` +
                        `<label class="sep"> : </label>` +
                        `<span class="htype">${hyp.htype}</span><br/>`;
                }).reduce((acc, cur) => acc + cur, "") +
                '</div>' +
                '<hr/>' +
                `<div class="pp_goals">` +
                    `<label class="numGoal">${itr}</label>` +
                    `<label class="sep"> : </label>` +
                    `<span class="goal">${goalStr}</span>` +
                    `<label class ="sep"></label><br/><br/>` +
                `</div>`;
    }).reduce((acc, cur) => acc + cur, "");
}

// number of write operations todo on the pseudoterminal
let ptyWriteCnt = 0;

function updateTerminalText(logstr: string){
    logstr = logstr.replace(/^[\n \t\r]*(\u001b\[[0-9]+m)[\n \t\r]*/g, "$1")
                   .replace(/[\n \t\r]*(\u001b\[[0-9]+m)[\n \t\r]*$/g, "$1");
    const termName = "Lambdapi Debug";
    const clearTextSeq = '\x1b[2J\x1b[3J\x1b[;H';

    let term = window.terminals.find((t) => t.name == termName);
    if(!term){
        const writeEmitter = new EventEmitter<string>();
        const pty : Pseudoterminal = {
            onDidWrite: writeEmitter.event,
            open: () => {},
            close: () => {},
            handleInput: (data: string) => {
                if(ptyWriteCnt > 0){
                    ptyWriteCnt--;
                    data = data.replace(/\r/g, '\r\n');
                    writeEmitter.fire(data);
                }
            }
        };
        term = window.createTerminal({name: termName, pty});
        term.show(true);
    }

    // increase ptyWriteCnt to allow write operation on pseudoterminal
    ptyWriteCnt++; term.sendText(clearTextSeq);
    ptyWriteCnt++; term.sendText(logstr);
}

// Returns the HTML code of the panel and the inset ccontent
function buildGoalsContent(goals : Goal[], styleUri : Uri) {
    
    let header, footer : String;

    // get the HTML code of goals environment
    let codeEnvGoals : String = getGoalsEnvContent(goals);

    // Use #FA8072 color too?

    return `
    <!DOCTYPE html>
    <html lang="en">
    <head>
        <meta charset="UTF-8">
        <link rel="stylesheet" type="text/css" href="${styleUri}" >
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <title>Goals</title>
    </head>
    <body>
        <p class="goals_env"> 
        ${codeEnvGoals}
        </p>
    </body>
    </html>`;
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
    hyps : Env[] // hypotheses
}

export interface UnifGoal extends Goal {
    constr : String
}

export interface TypGoal extends Goal {
	gid :  String // goal id
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
        
        updateTerminalText(goals.logs);

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
