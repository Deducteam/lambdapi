# Requirements: pygmentize -V >= 2.2.0 (http://pygments.org/)

# This file should be added in your LaTeX project. Then, one can use:
# \usepackage{minted}
# \begin{minted}{dedukti.py:DeduktiLexer -x}
#   ...
# \end{minted}

import re

from pygments.lexer import RegexLexer, default, words, bygroups
from pygments.token import Text, Comment, Operator, Keyword, Name, String, \
    Number, Punctuation, Generic

class DeduktiLexer(RegexLexer):
    """
    For the Dedukti language

    .. versionadded:: 0.1
    """

    name = 'Dedukti'
    aliases = ['dedukti']
    filenames = ['*.dk']
    mimetypes = ['text/x-dedukti']

    keywords = (
        'def', 'thm', 'private'
    )

    keyopts = (
        '->', ':', ':=', '-->','\.', '=>'
    )

    parens = (
        '\(', '\)','\[','\]',','
    )

    command = (
        "#NAME", "#WHNF", "#SNF", "#INFER", "#CHECK", "#ASSERT", "#CONV", "#PRINT"
    )

    tokens = {
        'root': [
            (r'\s+', Text),
            (r'\(\;(?![)])', Comment, 'comment'),
            (r'(%s)' % '|'.join(parens), Keyword.Pseudo),
            (r'Type', Keyword.Type),
            (r'(%s)' % '|'.join(keyopts[::-1]), Name.Builtin.Pseudo),
            (r'(def|thm|private|private def)'
             r'(\s\s*)'
             r'([^\W][\w0-9\'\?]*)'
             r'(\s*)'
             r'(:=|:)',
             bygroups(Keyword, Text, Name.Function, Text, Operator.Word)),
            (r'(%s)' % '|'.join(keywords), Keyword),
            (r'(^[^\W][\?\w0-9]*)(\s*)(:|:=)', bygroups(Name.Function, Text, Operator.Word)),
            (r'(%s)' % '|'.join(command), String.Symbol),
            (r'"', String.Double, 'string'),
            (r"[^\W][\w']*", Name),
        ],
        'comment': [
            (r'[^(;)]+', Comment),
            (r'\(\;', Comment, '#push'),
            (r'\;\)', Comment, '#pop'),
            (r'[(;)]', Comment),
        ],
        'string': [
            (r'[^"]+', String.Double),
            (r'""', String.Double),
            (r'"', String.Double, '#pop'),
        ],
    }
