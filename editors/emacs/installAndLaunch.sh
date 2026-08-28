#!/bin/bash

set -e

EGLOT_V="$1" # "0" to use the latest version
MATH_SYMB_V="$2" # "0" to use the latest version
HIGHLIGHT_V="$3" # "0" to use the latest version

# extracts from lambdapi-mode.el the smallest supported version of $pkg
#min_version_of_pkg() {
#    local pkg=$1
#    sed -n -E "/;; Package-Requires:/ s/.*\(\b${pkg}\b +\"([^\"]+)\"\).*/\1/p" lambdapi-mode.el
#}

EMACS=/snap/bin/emacs
if [[ ! -f $EMACS ]]; then
    echo "Install Emacs ..."
    sudo snap install emacs --classic
fi

ROOT=${ROOT=$HOME}

echo "Create $ROOT/.emacs.d/init.el ..."
mkdir -p $ROOT/.emacs.d/elpa
cat <<EOF > $ROOT/.emacs.d/init.el
(require 'package)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
(setq package-check-signature nil)
(add-to-list 'load-path (expand-file-name "$ROOT/.emacs.d/elpa/eglot/"))
(require 'eglot)
(add-to-list 'load-path (expand-file-name "$ROOT/.emacs.d/elpa/math-symbol-lists/"))
(require 'math-symbol-lists)
(add-to-list 'load-path (expand-file-name "$ROOT/.emacs.d/elpa/highlight/"))
(require 'highlight)
EOF

clone() {
    local url=$1
    local name=`basename $url .git`
    local dir=$ROOT/.emacs.d/elpa/$name
    if [[ -d "$dir" ]]; then
        echo "$name already cloned. Skipping."
    else
        git clone --depth 1 $url $dir
        echo "$name cloned to $dir."
    fi
}

commit_of() {
    local name=$1
    local version=$2
    local dir=$ROOT/.emacs.d/elpa/$name
    if [[ "$version" =~ ^.{8}\..{4}$ ]]; then
        git -C $dir rev-list -1 --after="$(printf "%s-%s-%s %s:%s\n" ${1:0:4} ${1:4:2} ${1:6:2} ${1:9:2} ${1:11:2})"
    else
        $version
    fi
}

branch() {
    local name=$1
    local version=$2
    local dir=$ROOT/.emacs.d/elpa/$name
    if [[ "$version" -ne 0 ]]; then
        git -C $dir checkout $(commit_of $version)
    else
        git -C $dir checkout master
        version=$(git -C $dir log -1 --format=%cd --date=format:'%Y%m%d.%H%M')
    fi
    echo "(define-package \"$name\" \"$version\")" > $ROOT/.emacs.d/elpa/$name/$name-pkg.el
}

checkout() {
    local url=$1
    local version=$2
    local name=`basename $url .git`
    clone $url
    branch $name $version
}

checkout https://github.com/joaotavora/eglot.git $EGLOT_V

checkout https://github.com/vspinu/math-symbol-lists.git $MATH_SYMB_V
touch $ROOT/.emacs.d/elpa/math-symbol-lists/math-symbol-lists-autoloads.el

checkout https://github.com/emacsmirror/highlight.git $HIGHLIGHT_V
touch $ROOT/.emacs.d/elpa/highlight/highlight-autoloads.el

echo "Install lambdapi-mode ..."
VERSION=$(sed -n 's/;; Version: //p' lambdapi-mode.el)
$EMACS --batch -l $ROOT/.emacs.d/init.el \
  --eval "(package-install-file \"lambdapi-mode-$VERSION.tar\")"

echo "🎉 Installation successful."
