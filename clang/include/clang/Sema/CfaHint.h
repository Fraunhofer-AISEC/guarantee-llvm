#ifndef LLVM_CLANG_SEMA_CFAHINT_H
#define LLVM_CLANG_SEMA_CFAHINT_H

#include "clang/Basic/IdentifierTable.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Sema/ParsedAttr.h"
#include "clang/Sema/Ownership.h"

namespace clang {
struct CfaHint {
  SourceRange Range;
  IdentifierLoc *PragmaNameLoc;
  IdentifierLoc *OptionLoc;

  CfaHint()
      : PragmaNameLoc(nullptr), OptionLoc(nullptr) {}
};

}
#endif // LLVM_CLANG_SEMA_CFAHINT_H
