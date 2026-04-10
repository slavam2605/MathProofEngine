import org.jetbrains.kotlin.gradle.dsl.KotlinJvmProjectExtension

plugins {
    application
    kotlin("jvm") version "2.3.20"
}

group = "dev.moklev.mathproof"
version = "0.1.0-SNAPSHOT"

allprojects {
    plugins.withId("org.jetbrains.kotlin.jvm") {
        extensions.configure<KotlinJvmProjectExtension>("kotlin") {
            compilerOptions {
                freeCompilerArgs.add("-Xcontext-parameters")
            }
        }
    }
}

repositories {
    mavenCentral()
}

dependencies {
    implementation(project(":algebra"))
    implementation(project(":core-engine"))
    implementation(project(":equality"))
    implementation(project(":fol"))
    implementation(project(":logic"))
    implementation(project(":nat"))
    implementation("org.jline:jline:3.25.1")
    testImplementation(kotlin("test"))
    testImplementation(testFixtures(project(":core-engine")))
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

tasks.register<JavaExec>("statementExplorer") {
    group = "application"
    description = "Interactive statement explorer for axioms and lemmas."
    classpath = sourceSets.main.get().runtimeClasspath
    mainClass.set("dev.moklev.mathproof.tools.StatementExplorerKt")
    standardInput = System.`in`
}
