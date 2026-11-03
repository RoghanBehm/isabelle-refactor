#!/bin/bash
set -e

REPO="$(cd "$(dirname "$0")" && pwd)"
cd "$REPO"

rm -rf classes jarroot Isabelle_Refactor.jar
mkdir -p classes jarroot

isabelle scalac -d classes src/isabelle/jedit/*.scala

cp -r classes/* jarroot/
cp actions.xml refactor.props plugin.props jarroot/

jar cf Isabelle_Refactor.jar -C jarroot .
cp Isabelle_Refactor.jar "$(isabelle getenv -b ISABELLE_HOME_USER)/jedit/jars/"

isabelle components -u "$REPO"
