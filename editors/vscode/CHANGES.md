All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## Unreleased

### Added

### Fixed

### Changed
- When calling lambdapi to lunch the lsp server from the Vscode extension, read the `lsp` argument from `package.json` instead of hard-coding it to allow using a custom command to lunch the server especially in Windows as discussed in issue #1163 (Many thanks to Akihisa Yamada)

## [0.2.2]
- code refactoring of the client for maintenability.
- fix the bug that causes the proof navigation to malfunction when the `Goals` panel is closed by the user. Now the panel is recreated whenever needed. If focus is taken away frol the `Goals` panel, focus is given back to it when user starts navigating proofs again.
- fix bug related to navigating sub-goals : navigating next subgoal stops before `{` instead of after it so that next subgoal is correctly shown in the `Goals` panel.
- change navigation with ``navigate until cursor`` : Navigation includes the command if the cursor is whithin its range instead of the line above. 
- first command is no more systematically navigated. If the current command is the first one, navigating the previous command results in no command being navigated.

## [0.1.2] - 2020-12-10
- use vscode configuration for lambdapi.path to call the lambdapi LSP server

## [0.1.1] - 2020-12-09

### Fixed
- fix backquotes in README.md

## [0.1.0] - 2020-12.09
- first release on the Marketplace
