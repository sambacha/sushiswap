import '@sushiswap/ui/index.css'

import { ChainId } from '@sushiswap/chain'
import { useLatestBlockNumber } from '@sushiswap/hooks'
import { App, Container, SushiIcon } from '@sushiswap/ui'
import { client, getProviders, Wallet } from '@sushiswap/wallet-connector'
import { Updater as MulticallUpdater } from 'lib/state/MulticallUpdater'
import { Updater as TokenListsUpdater } from 'lib/state/TokenListsUpdater'
import type { AppProps } from 'next/app'
import Link from 'next/link'
import { useRouter } from 'next/router'
import { FC, useMemo } from 'react'
import { Provider } from 'react-redux'
import { store } from 'store'
import { WagmiProvider } from 'wagmi'

const SUPPORTED_CHAIN_IDS = [
  // ChainId.ETHEREUM,
  // ChainId.BSC,
  // ChainId.AVALANCHE,
  // ChainId.POLYGON,
  ChainId.ARBITRUM,
  ChainId.OPTIMISM,
  // ChainId.FANTOM,
  // TESTNETS
  // ChainId.POLYGON_TESTNET,
  // ChainId.RINKEBY,
  // ChainId.ROPSTEN,
  // ChainId.GÖRLI,
  // ChainId.KOVAN,
]

const MyApp: FC<AppProps> = ({ Component, pageProps }) => {
  const router = useRouter()
  const [
    // providerEthereum,
    // providerBsc,
    // providerAvalanche,
    // providerPolygon,
    providerArbitrum,
    providerOptimism,
    // providerFantom,
    // providerPolygonTestnet,
    // providerRinkeby,
    // providerRopsten,
    // providerGorli,
    // providerKovan,
  ] = getProviders(SUPPORTED_CHAIN_IDS)

  // const blockNumberEthereum = useLatestBlockNumber(providerEthereum)
  // const blockNumberBsc = useLatestBlockNumber(providerBsc)
  // const blockNumberAvalanche = useLatestBlockNumber(providerAvalanche)
  // const blockNumberPolygon = useLatestBlockNumber(providerPolygon)
  const blockNumberArbitrum = useLatestBlockNumber(providerArbitrum)
  const blockNumberOptimism = useLatestBlockNumber(providerOptimism)

  // const blockNumberFantom = useLatestBlockNumber(providerFantom)
  // const blockNumberPolygonTestnet = useLatestBlockNumber(providerPolygonTestnet)
  // const blockNumberRinkeby = useLatestBlockNumber(providerRinkeby)
  // const blockNumberRopsten = useLatestBlockNumber(providerRopsten)
  // const blockNumberGorli = useLatestBlockNumber(providerGorli)
  // const blockNumberKovan = useLatestBlockNumber(providerKovan)
  const blockNumbers = useMemo(
    () => [
      // blockNumberEthereum,
      // blockNumberPolygon,
      blockNumberArbitrum,
      blockNumberOptimism,
      // blockNumberPolygonTestnet,
      // blockNumberRinkeby,
      // blockNumberRopsten,
      // blockNumberGorli,
      // blockNumberKovan,
    ],
    [
      // blockNumberEthereum,
      // blockNumberPolygon,
      blockNumberArbitrum,
      blockNumberOptimism,
      // blockNumberPolygonTestnet,
      // blockNumberRinkeby,
      // blockNumberRopsten,
      // blockNumberGorli,
      // blockNumberKovan,
    ]
  )

  // console.log({
  //   blockNumberEthereum,
  //   blockNumberPolygon,
  //   blockNumberArbitrum,
  //   blockNumberRinkeby,
  //   blockNumberRopsten,
  //   blockNumberGorli,
  //   blockNumberKovan,
  // })

  return (
    <WagmiProvider client={client}>
      <Provider store={store}>
        <App.Shell>
          <div className="border-b border-slate-700">
            <Container maxWidth="full" className="px-2">
              <App.Header
                className="h-[54px]"
                brand={
                  <Link href="/">
                    <a>
                      <SushiIcon width={32} height={32} className="mr-1 hover:animate-spin hover:text-pink" />
                    </a>
                  </Link>
                }
              >
                <Wallet.Button />
              </App.Header>
            </Container>
          </div>
          {/* <MulticallUpdater chainId={ChainId.ETHEREUM} blockNumber={blockNumberEthereum} />/ */}
          {/* <MulticallUpdater chainId={ChainId.BSC} blockNumber={blockNumberBsc} /> */}
          {/* <MulticallUpdater chainId={ChainId.AVALANCHE} blockNumber={blockNumberAvalanche} /> */}
          {/* <MulticallUpdater chainId={ChainId.POLYGON} blockNumber={blockNumberPolygon} /> */}
          {/* <MulticallUpdater chainId={ChainId.ARBITRUM} blockNumber={blockNumberArbitrum} /> */}
          {/* <MulticallUpdater chainId={ChainId.OPTIMISM} blockNumber={blockNumberOptimism} /> */}
          {/* <MulticallUpdater chainId={ChainId.FANTOM} blockNumber={blockNumberFantom} /> */}
          {/* <MulticallUpdater chainId={ChainId.POLYGON_TESTNET} blockNumber={blockNumberPolygonTestnet} /> */}
          {/* <MulticallUpdater chainId={ChainId.RINKEBY} blockNumber={blockNumberRinkeby} /> */}
          <MulticallUpdater chainId={ChainId.ARBITRUM} />
          <MulticallUpdater chainId={ChainId.OPTIMISM} />

          {/* <MulticallUpdater chainId={ChainId.ROPSTEN} blockNumber={blockNumberRopsten} /> */}
          {/* <MulticallUpdater chainId={ChainId.GÖRLI} blockNumber={blockNumberGorli} /> */}
          {/* <MulticallUpdater chainId={ChainId.KOVAN} blockNumber={blockNumberKovan} /> */}
          {/* <TokenListsUpdater chainId={ChainId.POLYGON_TESTNET} /> */}
          {/* <TokenListsUpdater chainId={ChainId.RINKEBY} /> */}
          <TokenListsUpdater chainId={ChainId.ARBITRUM} />
          <TokenListsUpdater chainId={ChainId.OPTIMISM} />
          <Component {...pageProps} blockNumbers={blockNumbers} chainIds={SUPPORTED_CHAIN_IDS} />
        </App.Shell>
      </Provider>
    </WagmiProvider>
  )
}

export default MyApp