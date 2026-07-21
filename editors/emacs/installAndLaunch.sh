#!/bin/bash

set -e
NAME="$1" # lambdapi
VERSION="$2" # defined in lambdapi-mode.el
BIN="$3" # emacs binary, e.g. /snap/bin/emacs
EGLOT_V="$4" # "0" to use the latest version
MATH_SYMB_V="$5" # "0" to use the latest version
HIGHLIGHT_V="$6" # "0" to use the latest version

convertVersionToCommitDate() {
  local input="$1"
  local date_part=${input%%.*}
  printf "%s-%s-%s %s:%s\n" \
    "${date_part:0:4}" \
    "${date_part:4:2}" \
    "${date_part:6:2}"
}

echo "📦 Installing Emacs ..."
sudo snap install emacs --classic

echo "📁 Creating ~/.emacs.d/ ..."
mkdir -p ~/.emacs.d

echo "📝 Creating init.el ..."
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

echo "Creating ~/.emacs.d/elpa/ ..."
mkdir -p ~/.emacs.d/elpa/

# [clone $branch $url] clones $url and checkout $branch (if <> 0) 
clone() {
    branch=$1
    url=$2
    name=`basename $url .git`
    dir=~/.emacs.d/elpa/$name
    if [ -d $dir ]; then
        echo "$name already cloned. Skipping."
    else
        if [[ $branch == "0" ]]; then
            git clone --depth 1 $url $dir
        else
            git clone --depth 1 --branch $branch $url $dir
        fi
        echo "$name cloned to $dir."
    fi
}

# [version $pkg] returns the version of $pkg in lambdapi-mode.el 
version() {
    pkg=$1
    sed -n -E "/;; Package-Requires:/ s/.*\(\b${pkg}\b +\"([^\"]+)\"\).*/\1/p" lambdapi-mode.el
}

clone $EGLOT_V https://github.com/joaotavora/eglot.git
if [[ $EGLOT_V == "0" ]]; then EGLOT_V=`version eglot`; fi

clone $MATH_SYMB_V https://github.com/vspinu/math-symbol-lists.git
if [[ $MATH_SYMB_V == "0" ]]; then MATH_SYMB_V=`version math-symbol-lists`; fi

clone $HIGHLIGHT_V https://github.com/emacsmirror/highlight.git
if [[ $HIGHLIGHT_V == "0" ]]; then HIGHLIGHT_V=`version highlight`; fi

echo "updating version in Elpa"
echo "(define-package \"highlight\" \"${HIGHLIGHT_V}\")" > ~/.emacs.d/elpa/highlight/highlight-pkg.el
echo "(define-package \"eglot\" \"${EGLOT_V}\")" > ~/.emacs.d/elpa/eglot/eglot-pkg.el
echo "(define-package \"math-symbol-lists\" \"${MATH_SYMB_V}\")" > ~/.emacs.d/elpa/math-symbol-lists/math-symbol-lists-pkg.el

touch ~/.emacs.d/elpa/math-symbol-lists/math-symbol-lists-autoloads.el
touch ~/.emacs.d/elpa/highlight/highlight-autoloads.el

echo "🚀 Install Emacs packages ..."
PATH="$BIN:$PATH" emacs \
  -l ~/.emacs.d/init.el \
  --eval "(package-install-file \"${NAME}-${VERSION}.tar\")" \
  --batch \
  # --eval "(require-package 'math-symbol-lists)" \
  echo "🎉 Emacs packages installed."
