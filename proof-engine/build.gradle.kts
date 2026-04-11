plugins {
    `java-library`
    `java-test-fixtures`
    kotlin("jvm") version "2.3.20"
}

group = "dev.moklev.mathproof"
version = "0.1.0-SNAPSHOT"

repositories {
    mavenCentral()
}

dependencies {
    api(project(":core"))
    testImplementation(kotlin("test"))
    testFixturesImplementation(kotlin("reflect"))
}

kotlin {
    jvmToolchain(21)
}

tasks.test {
    useJUnitPlatform()
}
