#ifndef OPCODE_H
#define OPCODE_H

enum OpCode {
    kOpCodeNop = 0x00,
    kOpCodePush = 0x01,
    kOpCodePop = 0x02,
    kOpCodePopn = 0x03,
    kOpCodeDup = 0x04,
    kOpCodeLoca = 0x0a,
    kOpCodeArga = 0x0b,
    kOpCodeGloba = 0x0c,
    kOpCodeLoad8 = 0x10,
    kOpCodeLoad16 = 0x11,
    kOpCodeLoad32 = 0x12,
    kOpCodeLoad64 = 0x13,
    kOpCodeStore8 = 0x14,
    kOpCodeStore16 = 0x15,
    kOpCodeStore32 = 0x16,
    kOpCodeStore64 = 0x17,
    kOpCodeAlloc = 0x18,
    kOpCodeFree = 0x19,
    kOpCodeStackalloc = 0x1a,
    kOpCodeAddI = 0x20,
    kOpCodeSubI = 0x21,
    kOpCodeMulI = 0x22,
    kOpCodeDivI = 0x23,
    kOpCodeAddF = 0x24,
    kOpCodeSubF = 0x25,
    kOpCodeMulF = 0x26,
    kOpCodeDivF = 0x27,
    kOpCodeDivU = 0x28,
    kOpCodeShl = 0x29,
    kOpCodeShr = 0x2a,
    kOpCodeAnd = 0x2b,
    kOpCodeOr = 0x2c,
    kOpCodeXor = 0x2d,
    kOpCodeNot = 0x2e,
    kOpCodeCmpI = 0x30,
    kOpCodeCmpU = 0x31,
    kOpCodeCmpF = 0x32,
    kOpCodeNegI = 0x34,
    kOpCodeNegF = 0x35,
    kOpCodeItof = 0x36,
    kOpCodeFtoi = 0x37,
    kOpCodeShrl = 0x38,
    kOpCodeSetLt = 0x39,
    kOpCodeSetGt = 0x3a,
    kOpCodeBr = 0x41,
    kOpCodeBrFalse = 0x42,
    kOpCodeBrTrue = 0x43,
    kOpCodeCall = 0x48,
    kOpCodeRet = 0x49,
    kOpCodeCallname = 0x4a,
    kOpCodeScanI = 0x50,
    kOpCodeScanC = 0x51,
    kOpCodeScanF = 0x52,
    kOpCodePrintI = 0x54,
    kOpCodePrintC = 0x55,
    kOpCodePrintF = 0x56,
    kOpCodePrintS = 0x57,
    kOpCodePrintln = 0x58,
    kOpCodePanic = 0xfe,
};

#endif // OPCODE_H
