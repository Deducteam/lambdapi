#!/bin/bash

set -e
NAME="$1"
VERSION="$2"
BIN="$3"

echo "🔧 Mise à jour du système..."
# sudo apt update && sudo apt install -y git curl

echo "📦 Installation d'Emacs..."
sudo snap install emacs --classic

echo "📁 Préparation du dossier de configuration Emacs..."
mkdir -p ~/.emacs.d

echo "📝 Écriture du fichier init.el avec straight.el et Eglot 1.17..."
cat <<'EOF' > ~/.emacs.d/init.el
(require 'package)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
(setq package-check-signature nil)
(use-package eglot)
(use-package math-symbol-lists)
(use-package highlight)

EOF
echo "🚀 Premier lancement d’Emacs pour déclencher l’installation..."
# (package-refresh-contents)
PATH="$BIN:$PATH" emacs \
  -l ~/.emacs.d/init.el \
  --eval "(require-package 'math-symbol-lists)" \
  # --batch \
  # --eval "(package-install-file \"${NAME}-${VERSION}.tar\")"
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


