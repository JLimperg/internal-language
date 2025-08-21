import Lake
open Lake DSL

package InternalLanguage

@[default_target]
lean_lib InternalLanguage

require aesop from git "https://github.com/JLimperg/aesop" @ "master"
require Qq from git "https://github.com/gebner/quote4" @ "master"
