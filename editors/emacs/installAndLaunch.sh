#!/bin/bash

set -e
NAME="$1"
VERSION="$2"
BIN="$3"
EGLOT_V="$4"
MATH_SYMB_V="$5"
HIGHLIGHT_V="$6"

# For using the latest commit of a library just use "0". For instance: ./installAndLaunch.sh lambdapi-mode 1.1.0 /snap/bin/emacs 0 1.3 0

# "./installAndLaunch.sh lambdapi-mode 1.1.0 /snap/bin/emacs 1.5 1.3 20210318.2248" does not work because eglot.1.5 is too old
# "./installAndLaunch.sh lambdapi-mode 1.1.0 /snap/bin/emacs 1.18 1.3 20210318.2248" does not work because eglot stoped using tags in 2012

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

echo "Cloning dependencies repos"
if [ ! -d ~/.emacs.d/elpa/eglot ]; then
  if [[ ${EGLOT_V} == "0" ]]; then  # ignore branch
    git clone --depth 1 https://github.com/joaotavora/eglot.git ~/.emacs.d/elpa/eglot
    #EGLOT_V=1.9
  else
    git clone --depth 1 --branch ${EGLOT_V} https://github.com/joaotavora/eglot.git ~/.emacs.d/elpa/eglot
  fi
  echo "Eglot cloned to " ~/.emacs.d/elpa/eglot
else
  echo "Eglot is already cloned. Skipping"
fi

if [ ! -d ~/.emacs.d/elpa/math-symbol-lists ]; then
  if [[ ${MATH_SYMB_V} == "0" ]]; then
    git clone --depth 1 https://github.com/vspinu/math-symbol-lists.git ~/.emacs.d/elpa/math-symbol-lists
    #MATH_SYMB_V=1.3
  else
    git clone --depth 1 --branch v${MATH_SYMB_V} https://github.com/vspinu/math-symbol-lists.git ~/.emacs.d/elpa/math-symbol-lists
  fi
  echo "math-symbol-lists cloned to " ~/.emacs.d/elpa/math-symbol-lists
else
  echo "math-symbol-lists is already cloned. Skipping"
fi

if [ ! -d ~/.emacs.d/elpa/highlight ]; then
  commit_date=$(convertVersionToCommitDate ${HIGHLIGHT_V})
  if [[ ${HIGHLIGHT_V} == "0" ]]; then
    git clone https://github.com/emacsmirror/highlight.git ~/.emacs.d/elpa/highlight
    #HIGHLIGHT_V=20250815.1830
  else
    git -C ~/.emacs.d/elpa/highlight checkout $(git -C ~/.emacs.d/elpa/highlight rev-list -n 1 --after="${commit_date}" master)
  fi
  echo "highlight cloned to " ~/.emacs.d/elpa/highlight
else
  echo "Highlight is already cloned. Skipping"
fi

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
