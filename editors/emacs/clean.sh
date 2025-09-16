#!/bin/bash

set -e

sudo apt remove --purge emacs emacs-common
sudo snap remove --purge emacs
echo removing conf files
rm -rf ~/.emacs.d ~/.emacs ~/.emacs.el ~/.config/emacs