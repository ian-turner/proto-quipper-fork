" Creating syntax groups
syntax keyword dpqBasicType Qubit Vec Nat VNil VCons Circ
syntax keyword dpqKeyword module where import
syntax keyword dpqSpecial forall else in for let reverse box unbox boxCirc controlled case of then if
syntax match dpqOperator "[\*!=:]"
syntax match dpqOperator "->"
syntax match dpqNumber /\c\<\%(\d\+\%(e[+-]\=\d\+\)\=\|0b[01]\+\|0o\o\+\|0x\%(\x\|_\)\+\)n\=\>/
syntax match dpqDouble /\c\<\%(\d\+\.\d\+\|\d\+\.\|\.\d\+\)\%(e[+-]\=\d\+\)\=\>/
syntax region dpqString start=+"\|c"+ skip=+\\\\\|\\"+ end=+"+ contains=@Spell
syntax match dpqInlineComment "--.*\n"

" Linking highlighting
highlight link dpqKeyword Keyword
highlight link dpqBasicType Type
highlight link dpqOperator Operator
highlight link dpqSpecial Identifier
highlight link dpqNumber Number
highlight link dpqDouble Double
highlight link dpqString String
highlight link dpqInlineComment Comment
highlight link dpqComment Comment
