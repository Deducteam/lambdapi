// VSCode extension for https://github.com/Deducteam/lambdapi
// a proof assistant based on the λΠ-calculus modulo rewriting

import {
    workspace,
    ExtensionContext,
    Position,
    Uri,
    commands,
    window,
    WebviewPanel,
    ViewColumn,
    TextEditor,
    TextDocument,
    SnippetString,
    Range,
    TextEditorDecorationType,
    Pseudoterminal,
    EventEmitter,
    TreeItemCollapsibleState,
    WebviewViewProvider,
    CancellationToken,
    WebviewView,
    WebviewViewResolveContext,
    TextDocumentChangeEvent,
    Diagnostic,
    languages,
    WorkspaceConfiguration
} from 'vscode';

// Insiders API, disabled
// import { WebviewEditorInset } from 'vscode';

import {
    LspClientConfig,
    LspServerConfig,
    LSPDocumentSelector,
} from "./config";

import {
    BaseLanguageClient,
    LanguageClientOptions,
    RequestType,
    RevealOutputChannelOn,
    VersionedTextDocumentIdentifier,
} from "vscode-languageclient";

import {
    LanguageClient,
    NotificationType,
    TextDocumentIdentifier,
    RegistrationRequest,
    DocumentSymbolRequest,
} from 'vscode-languageclient/node';

import { assert, time } from 'console';

let client: BaseLanguageClient;

// Client Factory types
export type ClientFactoryType = (
    context: ExtensionContext,
    clientOptions: LanguageClientOptions,
    wsConfig: WorkspaceConfiguration,
    lspServerPath: any,
) => BaseLanguageClient;

// The implementation of the VSCode lambdapi extension commands.
function goToProofState(context: ExtensionContext) {

    const proofState: Position | undefined = context.workspaceState.get('proofState');
    if (!proofState) {
        console.log("goToProofState : proofState workspace variable not set properly");
        return;
    }

    commands.executeCommand('revealLine', { lineNumber: proofState.line, at: 'center' });
}

function toggleCursorMode(context: ExtensionContext): boolean {
    let cursorMode: boolean = context.workspaceState.get('cursorMode') ?? false;

    cursorMode = !cursorMode;
    context.workspaceState.update('cursorMode', cursorMode);

    if (cursorMode) {

        window.showInformationMessage("Cursor navigation enabled");

        //By default, follow mode is disabled in cursor mode (because it may be nausea-inducing)
        if (context.workspaceState.get('follow'))
            toggleFollowMode(context);
    }

    else {

        window.showInformationMessage("Cursor navigation disabled");

        //By default, follow mode is enabled when cursor mode is off (because it is more practical)
        if (!context.workspaceState.get('follow'))
            toggleFollowMode(context);
    }

    return cursorMode;
}

function toggleFollowMode(context: ExtensionContext): boolean {
    let follow: boolean = context.workspaceState.get('follow') ?? false;

    follow = !follow;
    context.workspaceState.update('follow', follow);


    if (follow)
        window.showInformationMessage("Window follows highlights");

    else
        window.showInformationMessage("Window doesn't follow highlights");

    return follow;
}

function checkProofForward(context: ExtensionContext) {

    //Checking workspace
    const openEditor: TextEditor | undefined = window.activeTextEditor;
    if (!openEditor)
        return;

    const proofState: Position | undefined = context.workspaceState.get('proofState');
    let panel: WebviewPanel | undefined | null = context.workspaceState.get('panel');

    if (!proofState) {
        console.log('checkProofForward : Workspace variables are not properly defined');
        return;
    }

    let newPos = stepCommand(openEditor.document, proofState, true);
    if (newPos)
        lpRefresh(context, newPos, panel, openEditor);
}

function checkProofBackward(context: ExtensionContext) {

    //Checking workspace
    const openEditor: TextEditor | undefined = window.activeTextEditor;
    if (!openEditor)
        return;

    const proofState: Position | undefined = context.workspaceState.get('proofState');
    const panel: WebviewPanel | undefined | null = context.workspaceState.get('panel');
    if (!proofState) {
        console.log('checkProofBackward : Workspace variables are not properly defined');
        return;
    }

    let newPos = stepCommand(openEditor.document, proofState, false);

    //Case the end has not been reached
    if (newPos)
        lpRefresh(context, newPos, panel, openEditor);
}

function checkProofUntilCursor(context: ExtensionContext) {

    //Checking workspace
    const openEditor: TextEditor | undefined = window.activeTextEditor;
    if (!openEditor)
        return;

    const proofState: Position | undefined = context.workspaceState.get('proofState');
    const panel: WebviewPanel | undefined | null = context.workspaceState.get('panel');

    if (!proofState) {
        console.log('checkProofUntilCursor : workspace variables are not properly defined');
        return;
    }

    //The current position of the cursor
    let cursorPosition: Position = openEditor.selection.active;

    cursorPosition = stepCommand(openEditor.document, cursorPosition, true);

    context.workspaceState.update('proofState', cursorPosition); //proof state is set to the cursor position

    refreshGoals(panel, openEditor, cursorPosition, context); //Goals panel is refreshed

    highlight(context, cursorPosition, openEditor);
}

function goToNextProof(context: ExtensionContext) {
    nextProof(context, true);
}

function goToPreviousProof(context: ExtensionContext) {
    nextProof(context, false);
}

function nextProof(context: ExtensionContext, direction: boolean) {

    //Checking workspace
    const openEditor: TextEditor | undefined = window.activeTextEditor;
    if (!openEditor) {
        console.log("No editor opened");
        return;
    }

    const proofState: Position | undefined = context.workspaceState.get('proofState');
    const panel: WebviewPanel | undefined | null = context.workspaceState.get('panel');

    if (!proofState) {
        console.log('nextProof : workspace variables are not properly defined');
        return;
    }

    //The position of the next proof
    let nextProofPos: Position = stepCommand(openEditor.document, proofState, direction, ['begin']);

    context.workspaceState.update('proofState', nextProofPos); //proof state is set to the position of the next proof keyword

    refreshGoals(panel, openEditor, nextProofPos, context); //Goals panel is refreshed

    highlight(context, nextProofPos, openEditor);
}

// Associate the command command to function fn defined above
function registerCommand(command: string, context: ExtensionContext, fn: (context: ExtensionContext) => void) {
    let disposable = commands.registerCommand(command, () => fn(context));
    context.subscriptions.push(disposable);
}

// This function is called by VSCode when the extension is activated
export function activateClientLSP(context: ExtensionContext,
    clientFactory: ClientFactoryType) {

    workspace.onDidChangeTextDocument((e) => {
        lpDocChangeHandler(e, context);
    })

    // Please refer to package.json section keybindings, to see the key binding corresponding to the following commands

    /*Toggle cursor mode (defaults to false)
    *if true, the "Proof" panel is updated when the cursor is moved
    *if false, updated when keybindings are pressed
    */
    registerCommand('extension.lambdapi.cursor', context, toggleCursorMode);
    //Navigate proof : step forward in a proof 
    registerCommand('extension.lambdapi.fw', context, checkProofForward);
    //Navigate proof : step backward in a proof
    registerCommand('extension.lambdapi.bw', context, checkProofBackward);
    //Navigate proof : move proof highlight to cursor
    registerCommand('extension.lambdapi.tc', context, checkProofUntilCursor);
    //Window follows proof or not
    registerCommand('extension.lambdapi.reveal', context, toggleFollowMode);
    //Center window on proof state
    registerCommand('extension.lambdapi.center', context, goToProofState);
    //Go to next/previous proof
    registerCommand('extension.lambdapi.nx', context, goToNextProof);
    registerCommand('extension.lambdapi.pv', context, goToPreviousProof);

    window.onDidChangeActiveTextEditor(e => {

        const proofState: Position | undefined = context.workspaceState.get('proofState');
        const panel: WebviewPanel | undefined | null = context.workspaceState.get('panel');

        if (!proofState || !panel) {
            console.log('onDidChangeActiveTextEditor : workspace variables are not properly defined');
            return;
        }

        refreshGoals(panel, e, proofState, context);
    });

    window.onDidChangeTextEditorSelection(e => {

        const cursorMode: boolean = context.workspaceState.get('cursorMode') ?? false;
        if (!cursorMode)
            return;

        checkProofUntilCursor(context);
    });

    //___Declaration of workspace variables___

    //Position of the proof cursor : colored highlights show until which point the proof was surveyed
    let proofState: Position = new Position(0, 0);
    context.workspaceState.update('proofState', proofState);

    //Cursor mode (proof cursor is the regular cursor) activated or not
    context.workspaceState.update('cursorMode', false);

    //The range of text to highlight
    let range: Range = new Range(new Position(0, 0), proofState);
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

    const wsConfig = workspace.getConfiguration("lambdapi");

    let client_version = context.extension.packageJSON.version;
    const initializationOptions = LspServerConfig.create(
        client_version,
        wsConfig
    );
    const clientOptions: LanguageClientOptions = {
        documentSelector: [
            { scheme: 'file', language: 'lp' },
            { scheme: "file", language: "markdown", pattern: "**/*.lp" },
        ],
        outputChannelName: "Lambdapi LSP Server Events",
        revealOutputChannelOn: RevealOutputChannelOn.Info,
        initializationOptions,
        markdown: { isTrusted: true, supportHtml: true },
    };

    // This function starts the client and the server
    const start = () => {

        let cP = new Promise<BaseLanguageClient>((resolve) => {
            // Create a client using the factory
            client = clientFactory(context, clientOptions, wsConfig, lspServerPath);
            resolve(client);
        });

        cP.then((client) => client.start().then(() => {
            // Create and show panel for proof goals
            createInfoPanel(context);
        })
        )

    };

    const stop = () => { }

    const restart = () => {
        // If the client is running then stop it before starting it again
        if (client) {
            client.stop();
        }

        start();

    };
    // associate the VSCode command "Lambdapi: restart the Lambdapi VSCode mode" with the restart function
    registerCommand('extension.lambdapi.restart', context, restart);

    start();
}

//This function creates the Goals panel when proofs are navigated
function createInfoPanel(context: ExtensionContext) {
    let panel: WebviewPanel | null = window.createWebviewPanel(
        'goals',
        'Goals',
        { preserveFocus: true, viewColumn: ViewColumn.Two },
        {}
    );
    // When the panel is closed for some reason, put null to reopen it when the user naviagate proofs again
    panel.onDidDispose(() => {
        context.workspaceState.update('panel', null);
    });
    context.workspaceState.update('panel', panel);
}

function lpDocChangeHandler(event: TextDocumentChangeEvent, context: ExtensionContext) {

    if (event.document != window.activeTextEditor?.document) {
        // should not happen
        console.log("Changes not on the active TextEditor");
        return;
    }
    let proofPos: Position | undefined = context.workspaceState.get('proofState');
    if (!proofPos) proofPos = new Position(0, 0);

    let firstChange: Position | undefined = undefined;
    for (let i = 0; i < event.contentChanges.length; i++) {
        let change = event.contentChanges[i];
        let changeStart: Position = change.range.start;
        if (firstChange != undefined)
            firstChange = changeStart.isBefore(firstChange) ? changeStart : firstChange;
        else
            firstChange = changeStart;
    }

    if (firstChange && firstChange.isBefore(proofPos)) {
        // region inside proved region is changed
        // update the proofState
        let newPos = stepCommand(event.document, firstChange, false);

        const panel: WebviewPanel | undefined | null = context.workspaceState.get('panel');
        if (!panel) {
            console.log('lpDocChangeHandler : workspace variables are not properly defined');
            return;
        }
        context.workspaceState.update('proofState', newPos);
        refreshGoals(panel, window.activeTextEditor, newPos, context);
        highlight(context, newPos, window.activeTextEditor);
    }
}

function getFirstError(uri: Uri, before?: Position) {
    let diags: Diagnostic[] = languages.getDiagnostics(uri);
    let firstError: Position | undefined = undefined;
    let ind = 0;
    for (let diag of diags) {
        if (diag.severity == 0) {//check if error
            if (firstError) {
                firstError = diag.range.start.isBefore(firstError) ? diag.range.start : firstError;
            } else {
                firstError = diag.range.start;
            }
        }
    }
    if (before) {
        if (firstError && firstError.isBefore(before)) return firstError;
        else return undefined;
    } else {
        return firstError;
    }
}

function highlight(context: ExtensionContext, newProofState: Position, openEditor: TextEditor) {


    //Highlighting text
    const proofDecoration: TextEditorDecorationType | undefined = context.workspaceState.get('proofDecoration');
    const errorDecoration: TextEditorDecorationType | undefined = context.workspaceState.get('errorDecoration');

    const firstError = getFirstError(openEditor.document.uri, newProofState);
    const zeroPos = new Position(0, 0);

    if (!proofDecoration || !errorDecoration)
        console.log('Highlights/decorations are not properly defined');
    else {
        if (firstError) {
            decorate(openEditor, new Range(zeroPos, firstError), proofDecoration);
            decorate(openEditor, new Range(firstError, newProofState), errorDecoration);
        } else {
            decorate(openEditor, null, errorDecoration);
            decorate(openEditor, new Range(zeroPos, newProofState), proofDecoration);
        }

    }
    //Scroll until last highlight (if follow mode is toggled)
    const follow: boolean | undefined = context.workspaceState.get('follow');

    if (follow)
        commands.executeCommand('revealLine', { lineNumber: newProofState.line, at: 'center' });
}

function lpRefresh(context: ExtensionContext, proofPos: Position, panel: WebviewPanel | null | undefined, openEditor: TextEditor) {

    context.workspaceState.update('proofState', proofPos);

    refreshGoals(panel, openEditor, proofPos, context); //Goals panel is refreshed

    highlight(context, proofPos, openEditor);
}

function decorate(openEditor: TextEditor, range: Range | null, decorationType: TextEditorDecorationType) {
    if (range)
        openEditor.setDecorations(decorationType, [range]);
    else
        openEditor.setDecorations(decorationType, []);
}

// returns the Position of next or previous command
function stepCommand(document: TextDocument, currentPos: Position, forward: boolean, terminators?: string[]) {

    if (terminators === undefined || terminators === null)
        terminators = [';', 'begin', '{'];

    let docBegin: Position = document.positionAt(0);
    let docEnd: Position = new Position(document.lineCount, 0);

    const minPos = (a: Position, b: Position) => a.compareTo(b) < 0 ? a : b;
    const maxPos = (a: Position, b: Position) => a.compareTo(b) > 0 ? a : b;
    const termRegex = new RegExp(terminators.join("|"), 'gi');

    let termPositions = [...document.getText().matchAll(termRegex)]
        .map(rm => { 
            if (rm[0] === ";") {
                return rm.index ? rm.index + rm[0].length : undefined
            }
            else return rm.index ? rm.index : undefined })
        .filter((x): x is number => x !== undefined) // remove undefined
        .map(x => document.positionAt(x));

    let nextCmdPos = termPositions
        .filter(p => currentPos.compareTo(p) * (forward ? 1 : -1) < 0)
        .reduce(forward ? minPos : maxPos, forward ? docEnd : docBegin);

    return nextCmdPos;
}

/*
This function is called when the server communicates new Goals to the client
The function checks first that the Goal panel is open and open a new one otherwise
*/
function refreshGoals(panel: WebviewPanel | null | undefined, editor: TextEditor | undefined, proofState: Position, context: ExtensionContext) {
    if (!editor) {
        return;
    }

    // Check the panel is open. Recreate it otherwise
    if (panel == null || !panel) {
        createInfoPanel(context);
        panel = context.workspaceState.get('panel')!;
    }

    const styleUri = panel!.webview.asWebviewUri(Uri.joinPath(context.extensionUri, 'media', 'styles.css'))
    sendGoalsRequest(proofState, panel!, editor.document.uri, styleUri);
}

// returns the HTML code of goals environment
function getGoalsEnvContent(goals: Goal[]) {

    if (goals.length == 0)
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

function updateTerminalText(logstr: string) {
    logstr = logstr.replace(/^[\n \t\r]*(\u001b\[[0-9]+m)[\n \t\r]*/g, "$1")
        .replace(/[\n \t\r]*(\u001b\[[0-9]+m)[\n \t\r]*$/g, "$1");
    const termName = "Lambdapi Debug";
    const clearTextSeq = '\x1b[2J\x1b[3J\x1b[;H';

    let term = window.terminals.find((t) => t.name == termName);
    if (!term) {
        const writeEmitter = new EventEmitter<string>();
        const pty: Pseudoterminal = {
            onDidWrite: writeEmitter.event,
            open: () => { },
            close: () => { },
            handleInput: (data: string) => {
                if (ptyWriteCnt > 0) {
                    ptyWriteCnt--;
                    data = data.replace(/\r/g, '\r\n');
                    writeEmitter.fire(data);
                }
            }
        };
        term = window.createTerminal({ name: termName, pty });
        term.show(true);
    }

    // increase ptyWriteCnt to allow write operation on pseudoterminal
    ptyWriteCnt++; term.sendText(clearTextSeq);
    ptyWriteCnt++; term.sendText(logstr);
}

// Returns the HTML code of the panel and the inset ccontent
function buildGoalsContent(goals: Goal[], styleUri: Uri) {

    let header, footer: String;

    // get the HTML code of goals environment
    let codeEnvGoals: String = getGoalsEnvContent(goals);

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

export interface TextDocumentIdent {
    uri: String
}

export interface ParamsGoals {
    textDocument: TextDocumentIdent // current text document
    position: Position         // position to get goals
}

export interface Env {
    hname: String // hypothesis name
    htype: String // hypothesis type
}

export interface Goal {
    typeofgoal: String // type of goal, values defined in lsp_base.ml
    hyps: Env[] // hypotheses
}

export interface UnifGoal extends Goal {
    constr: String
}

export interface TypGoal extends Goal {
    gid: String // goal id
    type: String // goals
}

export interface GoalResp {
    goals: Goal[]
    logs: string
}

// Build a request, send it to the server and update the Goals panel when the answer is received
function sendGoalsRequest(position: Position, panel: WebviewPanel, docUri: Uri, styleUri: Uri) {

    let doc = { uri: docUri.toString() }
    let cursor = { textDocument: doc, position: position };
    const req = new RequestType<ParamsGoals, GoalResp, void>("proof/goals");
    client.sendRequest(req, cursor).then((goals) => {

        updateTerminalText(goals.logs);

        if (goals.goals) {
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

// Deactivate the Lambdapi extension. Stop the client.
export function deactivateClientLSP(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    }
    return client.stop();
}
