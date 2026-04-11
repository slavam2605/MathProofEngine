plugins {
    kotlin("jvm") version "2.3.20"
}

group = "dev.moklev.mathproof"
version = "0.1.0-SNAPSHOT"

repositories {
    mavenCentral()
}

dependencies {
    implementation(project(":algebra"))
    implementation(project(":proof-engine"))
    implementation(project(":equality"))
    implementation(project(":fol"))
    implementation(project(":logic"))
    testImplementation(kotlin("test"))
    testImplementation(testFixtures(project(":proof-engine")))
}

kotlin {
    jvmToolchain(21)
}

tasks.test {
    useJUnitPlatform()
}
