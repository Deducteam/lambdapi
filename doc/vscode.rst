`VSCode`_
=========

You can get the VSCode extension for Lambdapi from the `Marketplace <https://marketplace.visualstudio.com/items?itemName=Deducteam.lambdapi>`__.
To install it from the sources, see `INSTALL.md <https://github.com/Deducteam/lambdapi/blob/master/editors/vscode/INSTALL.md>`__.

..
  the following is generated automatically from editors/vscode/README.md
  using https://cloudconvert.com/md-to-rst

The extension provides syntax highlighting,
go-to-definition, key-bindings for proof navigation, and snippets for
inputing common mathematical symbols.

Logs (command ``debug``) are displayed in a terminal which opens
automatically when needed.

**Proof navigation**

Goals are visualised in a panel on the right side of the editor. You can
navigate in proof with the following key-bindings:

-  ``Ctrl+Right``: go one step forward
-  ``Ctrl+Left``: go one step backward
-  ``Ctrl+Up``: go to the previous proof (or the beginning)
-  ``Ctrl+Down``: go to the next proof (or the end)
-  ``Ctrl+Enter``: go to the position of the cursor
-  ``Ctrl+Alt+c``: toggle cursor mode (proof highlight follows the
   cursor or not)
-  ``Ctrl+Alt+w``: toggle follow mode (proof highlight is always
   centered in the window when keybindings are pressed)
-  ``Shift+Alt+w``: center proof highlight in the current window

**Hover and go-to-definition**

Hovering a token will display its type if available. For the
go-to-definition, you can either:

-  press ``F12`` when the cursor is within the range of a certain symbol
-  or ``right-click`` on the symbol -> “Go to definition”. It is advised
   to set up a key-binding for “Go back” in File -> Preferences ->
   Keyboard shortcuts.

**Snippets**

Type one of the suggested snippets described below, then press ``Enter``
or ``Tab`` to confirm adding the chosen Unicode character. If a snippet
completion does not seem to work, try pressing ``Ctrl+Space`` to see
completion suggestions.

.. raw:: html

   <!-- In Markdown code, backquote is obtained by putting spaces around. -->

*Common symbols*: :literal:`\`ra`: →, :literal:`\`is`: ≔,
:literal:`\`re`: ↪, :literal:`\`all`: ∀, :literal:`\`ex`: ∃,
:literal:`\`imp`: ⇒, :literal:`\`or` : ∨, :literal:`\`and` : ∧,
:literal:`\`not` : ¬, :literal:`\`th`: ⊢, :literal:`\`eq`: ≡,
:literal:`\`box`: □, :literal:`\`cons`: ⸬

*Greek letters*: For every letter ``l``, typing :literal:`\`l` will
suggest a corresponding unicode greek letter (for instance
:literal:`\`b` will suggest β). Some greek letters are present in a
variant form as in LaTeX, accessible with :literal:`\`vl` (for instance,
:literal:`\`f` will suggest ϕ and :literal:`\`vf` will suggest φ).

*Fonts*: For every letter ``l``, the following prefixes change the font
of ``l``: :literal:`\`dl` for double-struck (ℕ), :literal:`\`il`: italic
(𝑁), :literal:`\`Il`: bold italic (𝑵), :literal:`\`sl`: script (𝒩 ),
:literal:`\`Sl`: bold script (𝓝), :literal:`\`fl`: Fraktur (𝔑).

**Recommended additional extension**

-  `unicode-math <https://marketplace.visualstudio.com/items?itemName=GuidoTapia2.unicode-math-vscode>`__
   replaces ``->`` by →, ``_1`` by ₁, and many other unicode characters
   by simply pressing ``Tab``.

.. _VSCode: https://code.visualstudio.com/
