0.0.9.0
-------

- First standalone release; code is the same, but we don't build a
  lambdapi package anymore.
- Logs : show an error message in Debug terminal if 
  the lambdapi.pkg is missing

0.0.8.7
-------
- [lambdapi] Rebase against 98fbf803959579dcb1e41989a33797aef10fac9b
- [core] Preliminary document type.
- [hover] Add basic hover protocol support.

0.0.8.6
-------
- [goals] Better information for display of goals in focus.

0.0.8.5
-------
- [improv] Try to refine symbol type.

0.0.8.4
-------
- [fix] Send correct `documentSymbol` `Location` object in response.

0.0.8.3
-----
- [fix] Get `documentSymbol`s at the completed document state.

0.0.8.2
-----
- Fix location info for new LP API.

0.0.8.1
-----
- Rebase against new `pureinterface` branch.

0.0.8
-----
- Preliminary support for `documentSymbol` request.

0.0.7.2
-----
- Support for emacs' [eglot](https://github.com/joaotavora/eglot).

0.0.7.1
-----
- Send hypothesis name and type separately.

0.0.7
-----
- Send structured goals in diagnostics.

0.0.6
-----
- Tweaked changelog.
- Better OPAM makefile script.
- Fix problem with `exit` call.

0.0.5
-----
- Updated lambdapi to pureinterface branch
- Fixed a few json object types bugs.
- Send goal information in simple form.

0.0.4
-----
- Fixed shutdown and exit calls

0.0.3
-----
- Improved protocol support by Ismail

0.0.2
-----
- Minor tweaks to packaging

0.0.1
-----
- Initial release of LambdaPI to OPAM
