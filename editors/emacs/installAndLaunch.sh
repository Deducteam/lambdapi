#!/bin/bash

set -e
NAME="$1"
VERSION="$2"
BIN="$3"
EGLOT_V="$4"
MATH_SYMB_V="$5"
HIGHLIGHT_V="$6"

# For instance, one can run the scrupt with /installAndLaunch.sh lambdapi-mode 1.1.0 /snap/bin/emacs 1.5 1.3 20210318.2248

echo "📦 Installation d'Emacs..."
sudo snap install emacs --classic

echo "📁 Préparation du dossier de configuration Emacs..."
mkdir -p ~/.emacs.d

echo "📝 Écriture du fichier init.el avec straight.el et Eglot 1.17..."
cat <<'EOF' > ~/.emacs.d/init.el
(require 'package)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
(setq package-check-signature nil)
(add-to-list 'load-path (expand-file-name "~/.emacs.d/elpa/eglot/"))
(require 'eglot)
(add-to-list 'load-path (expand-file-name "~/.emacs.d/elpa/math-symbol-lists/"))
(require 'math-symbol-lists)
(add-to-list 'load-path (expand-file-name "~/.emacs.d/elpa/highlight/"))
(require 'highlight)
EOF
 echo "creating elpa folder"
 mkdir -p ~/.emacs.d/elpa/

echo "cloning dependencies repos"
git clone --depth 1 --branch ${EGLOT_V} https://github.com/joaotavora/eglot.git ~/.emacs.d/elpa/eglot
git clone --depth 1 https://github.com/emacsmirror/highlight.git ~/.emacs.d/elpa/highlight
git clone --depth 1 --branch v${MATH_SYMB_V} https://github.com/vspinu/math-symbol-lists.git ~/.emacs.d/elpa/math-symbol-lists

echo "updating version in Elpa"
echo "(define-package \"highlight\" \"${HIGHLIGHT_V}\")" > ~/.emacs.d/elpa/highlight/highlight-pkg.el
echo "(define-package \"eglot\" \"${EGLOT_V}\")" > ~/.emacs.d/elpa/eglot/eglot-pkg.el
echo "(define-package \"math-symbol-lists\" \"${MATH_SYMB_V}\")" > ~/.emacs.d/elpa/math-symbol-lists/math-symbol-lists-pkg.el

touch ~/.emacs.d/elpa/math-symbol-lists/math-symbol-lists-autoloads.el
touch ~/.emacs.d/elpa/highlight/highlight-autoloads.el

echo "🚀 Premier lancement d’Emacs pour déclencher l’installation..."
# (package-refresh-contents)
PATH="$BIN:$PATH" emacs \
  -l ~/.emacs.d/init.el \
  --eval "(package-install-file \"${NAME}-${VERSION}.tar\")" \
  --batch \
#   # --eval "(require-package 'math-symbol-lists)" \
echo "🎉 Terminé ! Lance Emacs normalement pour commencer à coder avec Eglot 1.17."

# (use-package eglot)
# (use-package math-symbol-lists)
# (use-package highlight)
# (require-package eglot)
# (require-package math-symbol-lists)
# (require-package highlight)

# curl highilight and math-symbol-lists from https://elpa.gnu.org/packages/math-symbol-lists.html
# extract with tar --lzip -xvf math-symbol-lists-1.1.tar.lz
# or lzip -d math-symbol-lists-1.2.1.el.lz

# move to /home/abdelghani/.emacs.d/elpa/math-symbol-lists and /home/abdelghani/.emacs.d/elpa/highlight
# echo ";; -*- no-byte-compile: t; lexical-binding: nil -*-
#(define-package "highlight" "20210318.2248"
#  "Highlighting commands."
#  ()
#  :url "https://www.emacswiki.org/emacs/download/highlight.el"
#  :commit "28557cb8d99b96eb509aaec1334c7cdda162517f"
#  :revdesc "28557cb8d99b"
#  :keywords '("faces" "help" "local")
#  :maintainers '(("Drew Adams (concat \"drew.adams\" \"oracle\" \".com\"" . "\"@\" ")))
# " > elpa/highlight-20210318.2248/highlight-pkg.el
# echo ";; -*- no-byte-compile: t; lexical-binding: nil -*-
# (define-package "math-symbol-lists" "1.2.1"
#   "Lists of Unicode math symbols and latex commands."
#   ()
#   :url "https://github.com/vspinu/math-symbol-lists"
#   :commit "ac3eb053d3b576fcdd192b0ac6ad5090ea3a7079"
#   :revdesc "ac3eb053d3b5"
#   :keywords '("unicode" "symbols" "mathematics")
#   :authors '(("Vitalie Spinu" . "spinuvit@gmail.com"))
#   :maintainers '(("Vitalie Spinu" . "spinuvit@gmail.com")))
# " > elpa/math-symbol-lists/math-symbol-lists-pkg.el

# REplace versions in *-pkg.el files


# echo
# PATH="$BIN:$PATH" emacs \
#   --batch \
#   -l ~/.emacs.d/init.el \
#   --eval="(package-refresh-contents) "

# echo "\
# " >> ~/.emacs.d/init.el


