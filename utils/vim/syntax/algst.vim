" Syntax file for algebraic sessions
"
" Author: Janek Spaderna
" License: MIT

if exists('b:current_syntax')
  finish
endif

" Keyword chars are
"   * digits 0-9    (48-57)
"   * ascii letters a-z, A-Z
"   * underscore    (95)
"   * single quote  (39)
setlocal iskeyword=48-57,a-z,A-Z,39-39,95-95

syn case match
syn sync fromstart
syn spell notoplevel

syn keyword algstControl case match of with if then else
syn keyword algstKeyword dual dualof rec let in _
syn keyword algstDecl type data protocol
  \ nextgroup=algstKindAnnot
  \ skipwhite
  \ skipempty
syn keyword algstBuiltin select receive send new fork fork_

syn match algstKind contained "\<\([TSM][LU]\?\|P\)\>"

syn match algstKindAnnot "\<\k\+\s*:" 
      \ contained
      \ contains=algstCon,algstVar,algstOperator
      \ nextgroup=algstKind
      \ skipwhite

syn match algstQuantifier "∀\|\<forall\>"
      \ nextgroup=algstKindAnnot
      \ skipwhite

syn match algstCon "\<[A-Z]\k*\>"
syn match algstCon "\<End[!?]"
syn match algstVar "\<\([a-z]\k*\|_\k\+\)\>" contained

syn match algstOperator "[!?.|&:=\-+<>*\\/→⊸λ]\+"
syn match algstOperator "-o"

syn match algstImplicitName "^?\?\k\+" contained
      \ contains=algstOperator,algstVar
syn region algstVarDef start=/^?\?\k\+/ end=/=\@1=/
      \ contains=algstImplicitName,algstBrackets,algstOperator
syn match algstSignature "^?\?\k\+\(\n*\s\)*:"
      \ contains=algstVar,algstOperator

syn match algstDelim ","
syn region algstParens matchgroup=algstDelim
      \ start="(" end=")"
      \ contains=
      \ ALLBUT,
      \ @algstImportDefs,
      \ algstSignature,
      \ algstVar,
syn region algstBrackets matchgroup=algstDelim
      \ start="\[" end="\]"
      \ contains=
      \ ALLBUT,
      \ @algstImportDefs,
      \ algstSignature,
      \ algstVar,
syn region algstBraces matchgroup=algstDelim
      \ start="{" end="}"
      \ contains=TOP

syn match algstModuleName "\<\([A-Z]\k*\.\)*[A-Z]\k*\>" 
      \ contained
      \ nextgroup=algstImportList,algstImportListAll
      \ skipwhite
      \ skipempty
syn keyword algstImport import
      \ nextgroup=algstModuleName,algstImportAs
      \ skipwhite
      \ skipempty
syn keyword algstImportAs as
      \ contained
      \ nextgroup=algstBuiltin,algst
      \ skipwhite
      \ skipempty
syn match algstImportListAll "(\*)"
      \ contained
syn region algstImportList start="(" skip="(.\{-})" end=")"
      \ contained
      \ contains=
      \ algstKeyword,
      \ algstDecl,
      \ algstCon,
      \ algstImportItem
syn match algstImportItem "\<\k\+\>\|(\S\{-})"
      \ contained
      \ contains=algstVar,algstCon,algstParens
      \ nextgroup=algstImportAs
      \ skipwhite
      \ skipempty
syn cluster algstImportDefs 
      \ contains=
      \ algstImport,
      \ algstImportList,
      \ algstImportAs,
      \ algstImportItem,
      \ algstImportListAll,
      \ algstModuleName

syn match algstComment "--.*$"
syn region algstCommentBlock start="{-" end="-}"

syn match algstNumber "\<[0-9]\+\(\.[0-9]\+\)\?\>"
syn match algstChar "'\([^\\]\|\\[n'"]\)'"
syn region algstString start=/"/ skip=/\\"/ end=/"/

hi def link algstImport Include
hi def link algstImportAs Include
hi def link algstImportList Include
hi def link algstImportListAll Include
hi def link algstControl Conditional
hi def link algstModuleName Type
hi def link algstVar Identifier
hi def link algstCon Type
hi def link algstKeyword Keyword
hi def link algstDecl Statement
hi def link algstKind Constant
hi def link algstOperator Operator
hi def link algstDelim Delimiter
hi def link algstQuantifier Operator
hi def link algstComment Comment
hi def link algstCommentBlock Comment
hi def link algstBuiltin Function
hi def link algstNumber Number
hi def link algstChar Character
hi def link algstString String

let b:current_syntax = 'algst'
