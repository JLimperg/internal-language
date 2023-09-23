import Lake
open Lake DSL

package InternalLanguage

@[default_target]
lean_lib InternalLanguage

require aesop from git "https://github.com/JLimperg/aesop" @ "master"
require std from git "https://github.com/leanprover/std4" @ "main"
require Qq from git "https://github.com/gebner/quote4" @ "master"
