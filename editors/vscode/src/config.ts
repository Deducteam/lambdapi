import { DocumentSelector, ExtensionContext, workspace } from "vscode";

export interface LspServerConfig {
  client_version: string;
  eager_diagnostics: boolean;
  goal_after_tactic: boolean;
  show_info_messages: boolean;
  show_notices_as_diagnostics: boolean;
  admit_on_bad_qed: boolean;
  debug: boolean;
  unicode_completion: "off" | "normal" | "extended";
  max_errors: number;
  pp_type: 0 | 1 | 2;
  show_stats_on_hover: boolean;
  show_loc_info_on_hover: boolean;
  check_only_on_request: boolean;
}

export namespace LspServerConfig {
  export function create(
    client_version: string,
    wsConfig: any
  ): LspServerConfig {
    return {
      client_version: client_version,
      eager_diagnostics: wsConfig.eager_diagnostics,
      goal_after_tactic: wsConfig.goal_after_tactic,
      show_info_messages: wsConfig.show_info_messages,
      show_notices_as_diagnostics: wsConfig.show_notices_as_diagnostics,
      admit_on_bad_qed: wsConfig.admit_on_bad_qed,
      debug: wsConfig.debug,
      unicode_completion: wsConfig.unicode_completion,
      max_errors: wsConfig.max_errors,
      pp_type: wsConfig.pp_type,
      show_stats_on_hover: wsConfig.show_stats_on_hover,
      show_loc_info_on_hover: wsConfig.show_loc_info_on_hover,
      check_only_on_request: wsConfig.check_only_on_request,
    };
  }
}

export enum ShowGoalsOnCursorChange {
  Never = 0,
  OnMouse = 1,
  OnMouseAndKeyboard = 2,
  OnMouseKeyboardCommand = 3,
}

export interface LspClientConfig {
  show_goals_on: ShowGoalsOnCursorChange;
}

export namespace LspClientConfig {
  export function create(wsConfig: any): LspClientConfig {
    let obj: LspClientConfig = { show_goals_on: wsConfig.show_goals_on };
    return obj;
  }
}
export const LSPDocumentSelector: DocumentSelector = [
  { language: "lambdapi" },
  { language: "markdown", pattern: "**/*.lp" },
];
