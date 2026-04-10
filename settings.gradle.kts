plugins {
    id("org.gradle.toolchains.foojay-resolver-convention") version "1.0.0"
}
rootProject.name = "MathProofEngine"

include(":algebra")
include(":core-engine")
include(":equality")
include(":fol")
include(":logic")
