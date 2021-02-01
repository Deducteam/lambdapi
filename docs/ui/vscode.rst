`VSCode`_
=========

There is an extension for VSCode >= 1.37 derived from VSCoq. To install
it do from the ``lambdapi`` repository:

.. code:: bash

   cd editors/vscode/
   make clean
   make

This requires to have ``npm`` and ``node-typescript`` installed:

.. code:: bash

   sudo apt install npm node-typescript

*note*: as of today the vscode mode requires a full lambdapi install, it
won’t unfortunately run from a developer tree.

Overview
--------

This extension provides syntax highlighting, unicode characters easy
insertion and proof navigation as in CoqIde or ProofGeneral.

It is still under development, thus might be incomplete and buggy.

Features
--------

Proof navigation
^^^^^^^^^^^^^^^^

Goals are visualised in a panel on the right side of the editor.

* You can navigate the proof with `keybindings <#keybindings>`__.
* “Cursor mode” can be toggled to navigate the proof with the cursor, using `Ctrl+Alt+c`. Other keybindings are still available in this mode.

Hover and definition
^^^^^^^^^^^^^^^^^^^^

Hovering a token will display its type if available. The "Go to
definition" command is available, you can either :

* press `F12` when your cursor is within the range of a certain symbol
* `right-click` on the symbol -> "Go to definition". It is advised to
  set up a keybinding for "Go Back" in File -> Preferences -> Keyboard
  shortcuts.

Snippets
^^^^^^^^

Type one of the suggested snippets described below, then press Enter
or Tab to confirm adding the chosen Unicode character.

Greek letters
^^^^^^^^^^^^^

For any letter ``l``, typing ```l`` will suggest a corresponding unicode greek
letter (for instance ```b`` will suggest β). Some greek letters are present in a
“var” form as in LaTeX, accessible with ```vl`` (for instance, ```f`` will
suggest ϕ and ```vf`` will suggest φ).

Fonts
^^^^^

For any letter ``l``, the following prefixes change the font of ``l``
(for instance, ```dN`` is double struck ``N``, ℕ):

* ```dl``: double-struck (ℕ)
* ```il``: italic (𝑁)
* ```Il``: bold italic (𝑵)
* ```sl``: script (𝒩 )
* ```Sl``: bold script (𝓝)
* ```fl``: Fraktur (𝔑)

Common symbols
""""""""""""""

- ```or`` : ∨
- ```and`` : ∧
- ```not`` : ¬
- ```ra``: →
- ```re``: ↪
- ```is``: ≔
- ```eq``: ≡
- ```th``: ⊢
- ```all``: ∀
- ```ex``: ∃
- ```imp``: ⇒
- ```box``: □
- ```cons``: ⸬

Recommended extension
---------------------

`This
extension <https://marketplace.visualstudio.com/items?itemName=GuidoTapia2.unicode-math-vscode>`__
allows for replacing ``\->`` with →, ``\_1`` with the index ₁ and many other
unicode characters by simply pressing Tab.

Troubleshoot
------------

If snippet completion does not seem to work with the VS-Code Lambdapi
Extension or the recommended extension, try pressing ``Ctrl+Space`` to
see completion suggestions.

Outline
-------

The outline of the document with its user-defined symbols is available with :

1. ``Ctrl+Shift+E`` (or clicking on the ``explorer`` in left side-bar)
2. Clicking ``outline`` in the bottom left corner.

Keybindings
-----------

For proof navigation :

-  ``Ctrl+Right`` : go one step forward
-  ``Ctrl+Left`` : go one step backward
-  ``Ctrl+Up`` : go to the previous proof (or the beginning)
-  ``Ctrl+Down`` : go to the next proof (or the end)
-  ``Ctrl+Enter`` : go to the position of the cursor
-  ``Ctrl+Alt+c`` : toggle cursor mode (proof highlight follows the
   cursor or not)
-  ``Ctrl+Alt+w`` : toggle follow mode (proof highlight is always
   centered in the window when keybindings are pressed)
-  ``Shift+Alt+w`` : center proof highlight in the current window

Commands
--------

Proof navigation is also accessible via the command search bar
(``Ctrl+Shift+P``) and searching “Lambdapi”.

A command to restart the Lambdapi VS Code mode is available (can be
useful in case of bugs).

Hover
-----

Hovering symbols provides their type. This feature is still
experimental.

Logs
----

Logs are displayed in a terminal which opens automatically
when needed.


.. _VSCode: https://code.visualstudio.com/
