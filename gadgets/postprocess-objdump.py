import re, sys

MOV_SHIFT = re.compile(
    r'mov\.w'
    r'(\s+)'
    r'(\w+)'
    r',\s*'
    r'\2'
    r',\s*'
    r'(lsl|lsr)\s+(\S+)'
)

SKIP = re.compile(
    # Garbage
    r'file format'
    r'|Disassembly of section'
    # Jasmin does dynamic stack-aligning. Since ScVerif is purely symbolic this
    # breaks verification as ScVerfi forgets the associated memory region.
    # `lr` holds the sp in jasmin functions.
    #  r'|bic\.w\s+lr, lr, #\d+'
    # ScVerif can now cope with it :)
)

for line in sys.stdin:
    line = re.sub(r'@ 0x[0-9a-f]+$', '', line)
    # strip objdump comments starting with `# `.
    # ARM immediates are ignored as they have no whitespace after `#`.
    line = re.sub(r'[ \t]*#[ \t].*$', '', line)
    # rewrite 
    #   mov rx, ry, lsl #imm
    # into equivalent formulation
    #   lsl rx, ry, imm
    # which scverif understands.
    if SKIP.search(line):
        continue
    print(MOV_SHIFT.sub(r'\3.w\1\2, \2, \4', line), end='')