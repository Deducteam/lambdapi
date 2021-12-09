This extension provides support for the [Lambdapi](https://github.com/Deducteam/lambdapi) language and proof assistant. See the [User manual](https://lambdapi.readthedocs.io/) to know more about Lambdapi. The extension provides syntax highlighting, go-to-definition, key-bindings for proof navigation, and snippets for inputing common mathematical symbols.

**Proof navigation**

Goals are visualised in a panel on the right side of the editor.
You can navigate in proof with the following key-bindings:

- ``Ctrl+Right``: go one step forward
- ``Ctrl+Left``: go one step backward
- ``Ctrl+Up``: go to the previous proof (or the beginning)
- ``Ctrl+Down``: go to the next proof (or the end)
- ``Ctrl+Enter``: go to the position of the cursor
- ``Ctrl+Alt+c``: toggle cursor mode (proof highlight follows the cursor or not)
- ``Ctrl+Alt+w``: toggle follow mode (proof highlight is always centered in the window when keybindings are pressed)
- ``Shift+Alt+w``: center proof highlight in the current window

**Hover and go-to-definition**

Hovering a token will display its type if available.
For the go-to-definition, you can either:

* press `F12` when the cursor is within the range of a certain symbol
* or `right-click` on the symbol -> "Go to definition". It is advised to
set up a key-binding for "Go back" in File -> Preferences -> Keyboard shortcuts.

**Snippets**

Type one of the suggested snippets described below, then press
``Enter`` or ``Tab`` to confirm adding the chosen Unicode
character. If a snippet completion does not seem to work, try pressing
``Ctrl+Space`` to see completion suggestions.

*Common symbols*: `` `ra``: →, `` `is``: ≔, `` `re``: ↪, `` `all``: ∀, `` `ex``: ∃, `` `imp``: ⇒, `` `or`` : ∨, `` `and`` : ∧, `` `not`` : ¬, `` `th``: ⊢, `` `eq``: ≡, `` `box``: □, `` `cons``: ⸬

*Greek letters*: For every letter ``l``, typing `` `l`` will suggest a
corresponding unicode greek letter (for instance `` `b`` will suggest
β). Some greek letters are present in a variant form as in LaTeX,
accessible with `` `vl`` (for instance, `` `f`` will suggest ϕ and
`` `vf`` will suggest φ).

*Fonts*: For every letter ``l``, the following prefixes change the
font of ``l``: `` `dl`` for double-struck (ℕ), `` `il``: italic (𝑁),
`` `Il``: bold italic (𝑵), `` `sl``: script (𝒩 ), `` `Sl``: bold
script (𝓝), `` `fl``: Fraktur (𝔑).

**Recommended additional extension**

- [unicode-math](https://marketplace.visualstudio.com/items?itemName=GuidoTapia2.unicode-math-vscode) replaces ``->`` by →, ``_1`` by ₁, and many other unicode characters by simply pressing ``Tab``.
