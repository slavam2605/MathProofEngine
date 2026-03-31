plugins {
    application
    kotlin("jvm") version "2.3.20"
}

group = "dev.moklev.mathproof"
version = "0.1.0-SNAPSHOT"

repositories {
    mavenCentral()
}

dependencies {
    implementation(project(":core-engine"))
    implementation(project(":logic"))
    testImplementation(kotlin("test"))
    testImplementation(kotlin("reflect"))
}

kotlin {
    jvmToolchain(21)
}

application {
    mainClass = "dev.moklev.mathproof.MainKt"
}

tasks.test {
    useJUnitPlatform()
}
