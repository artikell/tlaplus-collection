#!/bin/bash

usage() {
    echo "Usage: $0 [options]"
    echo "Options:"
    echo "  -h, --help       Show this help message"
    echo "  -v, --version    Show version information"
    echo "  -d, --download   Download necessary files"
    echo "  -c, --check <module_name>  Check if the command for a module is valid"
    echo "  -a, --add <module_name>     Add a new module"
    echo "Examples:"
    echo "  $0 -v"
    echo "  $0 -d"
    echo "  $0 -c MyModule"
    echo "  $0 -a NewModule"
    echo "  $0 --help"
    echo "  $0 --version"
}

version() {
    git rev-parse --short HEAD 2>/dev/null || echo "Unknown version"
    echo "Commit date: $(git log -1 --format=%cd --date=short 2>/dev/null || echo "Unknown date")"
}

download() {
    echo "Downloading files..."
    # Add your download logic here
    wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -O tla2tools.jar || {
        echo "Failed to download tla2tools.jar"
        exit 1
    }
}

check_command() {
    module_name=$1
    if [[ -z "$module_name" ]]; then
        echo "Error: No module name provided."
        exit 1
    fi

    if [[ ! -d "$module_name" ]]; then
        echo "Error: Module '$module_name' does not exist."
        exit 1
    fi

    command -v "java" >/dev/null 2>&1 || {
        echo "Error: java is not installed."
        exit 1
    }

    if [[ ! -f $module_name/$module_name.cfg ]]; then
        java -jar tla2tools.jar -config model.cfg $module_name/$module_name.tla || {
            echo "Error: Command for module '$module_name' is not valid."
            exit 1
        }
    else
        java -jar tla2tools.jar -config $module_name/$module_name.cfg $module_name/$module_name.tla || {
            echo "Error: Command for module '$module_name' is not valid."
            exit 1
        }
    fi

    echo "Command for module '$module_name' is valid."
}

add_module() {
    module_name=$1
    if [[ -z "$module_name" ]]; then
        echo "Error: No module name provided."
        exit 1
    fi

    if [[ -d "$module_name" ]]; then
        echo "Error: Module '$module_name' already exists."
        exit 1
    fi

    mkdir -p "$module_name"
    echo "---- MODULE $module_name ----" > "$module_name/$module_name.tla"
    echo "====" >> "$module_name/$module_name.tla"
    echo "Module '$module_name' created successfully."

    java -jar tla2tools.jar -config model.cfg $module_name/$module_name.tla > /dev/null 2>&1 || {
        echo "Error: Failed to validate the module '$module_name'."
        exit 1
    }
}

transform() {
    module_name=$1
    if [[ -z "$module_name" ]]; then
        echo "Error: No module name provided."
        exit 1
    fi

    if [[ ! -d "$module_name" ]]; then
        echo "Error: Module '$module_name' does not exist."
        exit 1
    fi

    java -cp tla2tools.jar pcal.trans $module_name/$module_name.tla || {
        echo "Error: Transformation failed for module '$module_name'."
        exit 1
    }

    check_command "$module_name"
}

while [[ "$1" != "" ]]; do
    case $1 in
        -h | --help )
            usage
            exit 0
            ;;
        -v | --version )
            version
            exit 0
            ;;
        -d | --download )
            download
            exit 0
            ;;
        -c | --check )
            check_command "$2"
            exit 0
            ;;
        -a | --add )
            add_module "$2"
            exit 0
            ;;
        -t | --transform )
            transform "$2"
            exit 0
            ;;
        * )
            echo "Unknown option: $1"
            usage
            exit 1
            ;;
    esac
    shift
done