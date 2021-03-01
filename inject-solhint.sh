#!/bin/sh
echo "::group::SolHint"
echo '::set-output name=SELECTED_COLOR::green'
npx solhint contracts/**/**/*.sol
echo "::endgroup::"

