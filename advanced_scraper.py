import streamlit as st
import asyncio
import aiohttp
import logging
import json
import csv
import io
import random
import hashlib
import os
import re
import yaml
import threading
import schedule
import time
import pandas as pd
from datetime import datetime, timedelta
from pathlib import Path
from bs4 import BeautifulSoup, Comment
from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.chrome.options import Options as ChromeOptions
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from webdriver_manager.chrome import ChromeDriverManager
from fake_useragent import UserAgent
from urllib.parse import urljoin, urlparse
from urllib.robotparser import RobotFileParser
from PIL import Image
from io import BytesIO
import validators
from newspaper import Article
import nltk
from dataclasses import dataclass
from typing import Optional, List, Dict
import xml.etree.ElementTree as ET

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

@dataclass
class ScrapingConfig:
    max_depth: int = 2
    max_pages: int = 100
    respect_robots: bool = True
    follow_links: bool = False
    user_agent: Optional[str] = None
    timeout: int = 30
    max_retries: int = 3
    delay: float = 1.0
    screenshot: bool = False
    save_html: bool = False
    extract_metadata: bool = True
    extract_comments: bool = True
    extract_structured_data: bool = True
    max_connections: int = 100
    requests_per_second: int = 10
    cache_size: int = 1000
    cache_ttl: int = 24

class RateLimiter:
    def __init__(self, requests_per_second=10):
        self.rate = requests_per_second
        self.last_check = time.time()
        self.tokens = requests_per_second
        self._lock = asyncio.Lock()
        self.domain_limiters = {}

    async def acquire(self, domain=None):
        if domain:
            if domain not in self.domain_limiters:
                self.domain_limiters[domain] = {
                    'tokens': self.rate,
                    'last_check': time.time()
                }
            return await self._acquire_domain(domain)
        async with self._lock:
            now = time.time()
            time_passed = now - self.last_check
            self.tokens = min(self.rate, self.tokens + time_passed * self.rate)
            if self.tokens < 1:
                await asyncio.sleep(1 / self.rate)
                self.tokens = 1
            self.tokens -= 1
            self.last_check = now

    async def _acquire_domain(self, domain):
        async with self._lock:
            now = time.time()
            limiter = self.domain_limiters[domain]
            time_passed = now - limiter['last_check']
            limiter['tokens'] = min(self.rate, limiter['tokens'] + time_passed * self.rate)
            if limiter['tokens'] < 1:
                await asyncio.sleep(1 / self.rate)
                limiter['tokens'] = 1
            limiter['tokens'] -= 1
            limiter['last_check'] = now

class ResourceManager:
    def __init__(self, max_connections=100):
        self.active_connections = 0
        self.max_connections = max_connections
        self._lock = asyncio.Lock()

    async def acquire(self):
        async with self._lock:
            while self.active_connections >= self.max_connections:
                await asyncio.sleep(0.1)
            self.active_connections += 1

    async def release(self):
        async with self._lock:
            self.active_connections -= 1

class RetryHandler:
    def __init__(self, max_retries=3, base_delay=1):
        self.max_retries = max_retries
        self.base_delay = base_delay

    def get_delay(self, attempt):
        return self.base_delay * (2 ** attempt)

    async def execute_with_retry(self, func, *args, **kwargs):
        last_exception = None
        for attempt in range(self.max_retries):
            try:
                return await func(*args, **kwargs)
            except Exception as e:
                last_exception = e
                if attempt < self.max_retries - 1:
                    delay = self.get_delay(attempt)
                    logger.warning(f"Attempt {attempt + 1} failed: {str(e)}. Retrying in {delay}s")
                    await asyncio.sleep(delay)
                else:
                    logger.error(f"All retry attempts failed: {str(e)}")
                    raise last_exception

class ScraperMetrics:
    def __init__(self):
        self.metrics = {
            'requests_total': 0,
            'successful_requests': 0,
            'failed_requests': 0,
            'bytes_downloaded': 0,
            'response_times': [],
            'errors_by_type': {},
            'cache_hits': 0,
            'cache_misses': 0
        }
        self._lock = threading.Lock()

    def record_request(self, success: bool, response_time: float, bytes_downloaded: int, error_type: str = None):
        with self._lock:
            self.metrics['requests_total'] += 1
            if success:
                self.metrics['successful_requests'] += 1
            else:
                self.metrics['failed_requests'] += 1
                if error_type:
                    self.metrics['errors_by_type'][error_type] = \
                        self.metrics['errors_by_type'].get(error_type, 0) + 1
            self.metrics['bytes_downloaded'] += bytes_downloaded
            self.metrics['response_times'].append(response_time)

    def record_cache_hit(self):
        with self._lock:
            self.metrics['cache_hits'] += 1

    def record_cache_miss(self):
        with self._lock:
            self.metrics['cache_misses'] += 1

    def get_statistics(self) -> dict:
        with self._lock:
            response_times = self.metrics['response_times']
            return {
                'total_requests': self.metrics['requests_total'],
                'success_rate': (self.metrics['successful_requests'] /
                                 max(1, self.metrics['requests_total']) * 100),
                'avg_response_time': sum(response_times) / max(1, len(response_times)),
                'total_bytes_downloaded': self.metrics['bytes_downloaded'],
                'error_distribution': self.metrics['errors_by_type'],
                'cache_hit_rate': (self.metrics['cache_hits'] /
                                   max(1, self.metrics['cache_hits'] + self.metrics['cache_misses']) * 100)
            }

class EnhancedDataValidator:
    @staticmethod
    def clean_text(text):
        if not text:
            return ""
        text = re.sub(r'\s+', ' ', text.strip())
        text = re.sub(r'[^\w\s.,!?-]', '', text)
        return text

    @staticmethod
    def validate_url(url):
        return validators.url(url)

    @staticmethod
    def validate_email(email):
        return validators.email(email)

    @staticmethod
    def clean_html(html):
        soup = BeautifulSoup(html, 'html.parser')
        for element in soup(['script', 'style', 'iframe']):
            element.decompose()
        return str(soup)

    @staticmethod
    def sanitize_filename(filename):
        return re.sub(r'[^\w\-_.]', '_', filename)

    def validate_content(self, content: dict) -> tuple[bool, list]:
        errors = []
        required_fields = {'url', 'timestamp', 'content_type', 'data'}
        missing_fields = required_fields - set(content.keys())
        if missing_fields:
            errors.append(f"Missing required fields: {missing_fields}")
        if not self.validate_url(content.get('url', '')):
            errors.append("Invalid URL format")
        try:
            datetime.fromisoformat(content.get('timestamp', ''))
        except ValueError:
            errors.append("Invalid timestamp format")
        return len(errors) == 0, errors

class ContentExtractor:
    def __init__(self):
        try:
            nltk.data.find('tokenizers/punkt')
        except LookupError:
            nltk.download('punkt')

    def extract_article(self, url: str) -> dict:
        try:
            article = Article(url)
            article.download()
            article.parse()
            article.nlp()
            return {
                'title': article.title,
                'text': article.text,
                'summary': article.summary,
                'keywords': article.keywords,
                'authors': article.authors,
                'publish_date': article.publish_date,
                'top_image': article.top_image,
                'images': list(article.images),
                'movies': list(article.movies)
            }
        except Exception as e:
            logger.error(f"Error extracting article content: {str(e)}")
            return {}

    def extract_metadata(self, soup: BeautifulSoup) -> dict:
        metadata = {
            'meta_tags': {},
            'links': {},
            'scripts': [],
            'comments': [],
            'structured_data': []
        }
        for meta in soup.find_all('meta'):
            name = meta.get('name') or meta.get('property')
            if name:
                metadata['meta_tags'][name] = meta.get('content')
        for link in soup.find_all('link'):
            rel = link.get('rel')
            if rel:
                metadata['links'][str(rel)] = link.get('href')
        metadata['comments'] = [str(comment) for comment in
                                soup.find_all(string=lambda text: isinstance(text, Comment))]
        for script in soup.find_all('script', type='application/ld+json'):
            try:
                metadata['structured_data'].append(json.loads(script.string))
            except:
                continue
        return metadata

class WebScraper:
    def __init__(self):
        self.session_data = {}
        self.history = []
        self.config = ScrapingConfig()
        self.user_agent = UserAgent()
        self.metrics = ScraperMetrics()
        self.validator = EnhancedDataValidator()
        self.content_extractor = ContentExtractor()
        self.rate_limiter = RateLimiter(self.config.requests_per_second)
        self.resource_manager = ResourceManager(self.config.max_connections)
        self.retry_handler = RetryHandler(self.config.max_retries)
        self.init_cache()

    def init_cache(self):
        self.cache = {'data': {}, 'size': 0, 'max_size': self.config.cache_size}

    def cache_cleanup(self):
        if len(self.cache['data']) > (self.cache['max_size'] * 0.8):
            sorted_cache = sorted(self.cache['data'].items(), key=lambda x: x[1]['timestamp'])
            to_remove = sorted_cache[:int(self.cache['max_size'] * 0.2)]
            for key, _ in to_remove:
                del self.cache['data'][key]

    async def create_client_session(self):
        connector = aiohttp.TCPConnector(limit=self.config.max_connections, ttl_dns_cache=300)
        return aiohttp.ClientSession(
            connector=connector,
            timeout=aiohttp.ClientTimeout(total=self.config.timeout),
            headers={'User-Agent': self.config.user_agent or self.user_agent.random}
        )

    def get_chrome_driver(self):
        options = ChromeOptions()
        options.add_argument('--headless')
        options.add_argument('--no-sandbox')
        options.add_argument('--disable-dev-shm-usage')
        options.add_argument(f'--user-agent={self.config.user_agent or self.user_agent.random}')
        try:
            service = Service(ChromeDriverManager().install())
            return webdriver.Chrome(service=service, options=options)
        except Exception as e:
            logger.error(f"Failed to initialize WebDriver: {e}")
            return None

    async def scrape_website(self, url: str, content_type: str, form_selector: Optional[str] = None):
        if not self.validator.validate_url(url):
            raise ValueError("Invalid URL format")

        cached_content = self.load_from_cache(url)
        if cached_content:
            self.metrics.record_cache_hit()
            return cached_content

        self.metrics.record_cache_miss()
        progress_bar = st.progress(0)
        status_text = st.empty()

        try:
            driver = self.get_chrome_driver()
            if not driver:
                raise Exception("Failed to initialize WebDriver.")

            driver.get(url)
            await asyncio.sleep(2)  # Wait for page to load
            html = driver.page_source
            if html is None:
                raise ValueError("Failed to retrieve HTML content.")

            result = {
                'url': url,
                'timestamp': datetime.now().isoformat(),
                'content_type': content_type,
                'data': None,
                'metadata': None,
                'screenshots': [],
                'html_path': None
            }

            soup = BeautifulSoup(html, 'html.parser')
            if content_type == 'text':
                result['data'] = soup.get_text(separator='\n', strip=True)
            elif content_type == 'links':
                result['data'] = [{'text': a.text, 'href': a.get('href')} for a in soup.find_all('a', href=True)]
            elif content_type == 'images':
                result['data'] = [{'alt': img.get('alt', ''), 'src': img.get('src')} for img in
                                  soup.find_all('img', src=True)]
            else:
                raise ValueError(f"Unsupported content type: {content_type}")

            if result['data'] is None:
                raise ValueError("No data was extracted; please check selectors and content type.")

            progress_bar.progress(100)
            status_text.text('Scraping completed successfully!')
            return result

        except Exception as e:
            logger.error(f"Error during scraping: {str(e)}")
            raise e

        finally:
            if driver:
                driver.quit()
            await self.resource_manager.release()

    def save_to_cache(self, url, content):
        self.cache_cleanup()
        url_hash = hashlib.md5(url.encode()).hexdigest()
        self.cache['data'][url_hash] = {
            'content': content,
            'timestamp': datetime.now().isoformat(),
            'expires': (datetime.now() + timedelta(hours=self.config.cache_ttl)).isoformat()
        }

    def load_from_cache(self, url):
        url_hash = hashlib.md5(url.encode()).hexdigest()
        cached_data = self.cache['data'].get(url_hash)
        if cached_data:
            expires = datetime.fromisoformat(cached_data['expires'])
            if datetime.now() < expires:
                return cached_data['content']
            else:
                del self.cache['data'][url_hash]
        return None

    def get_metrics(self):
        return self.metrics.get_statistics()

    def clear_history(self):
        self.history = []

    def export_history(self, format='json'):
        if format == 'json':
            return json.dumps(self.history, indent=2, default=str)
        elif format == 'csv':
            output = io.StringIO()
            if self.history:
                flattened_data = []
                for item in self.history:
                    flat_item = {}
                    for key, value in item.items():
                        if isinstance(value, (dict, list)):
                            flat_item[key] = json.dumps(value)
                        else:
                            flat_item[key] = value
                    flattened_data.append(flat_item)
                writer = csv.DictWriter(output, fieldnames=flattened_data[0].keys())
                writer.writeheader()
                writer.writerows(flattened_data)
            return output.getvalue()

scraper = WebScraper()

def main():
    st.title("Enhanced Web Scraper")
    with st.sidebar:
        max_depth = st.slider("Max Crawl Depth", 1, 10, 2)
        max_pages = st.number_input("Max Pages", 1, 1000, 100)
        respect_robots = st.checkbox("Respect robots.txt", value=True)
        max_connections = st.slider("Max Connections", 10, 200, 100)
        requests_per_second = st.slider("Requests/Second", 1, 20, 10)
        cache_enabled = st.checkbox("Enable Cache", value=True)
        cache_ttl = st.slider("Cache TTL (hours)", 1, 72, 24)
        cache_size = st.slider("Cache Size", 100, 5000, 1000)
        if st.button("Update Configuration"):
            scraper.config = ScrapingConfig(
                max_depth=max_depth,
                max_pages=max_pages,
                respect_robots=respect_robots,
                max_connections=max_connections,
                requests_per_second=requests_per_second,
                cache_ttl=cache_ttl if cache_enabled else 0,
                cache_size=cache_size if cache_enabled else 0
            )
            st.success("Configuration updated!")
        metrics = scraper.get_metrics()
        st.write(f"Total Requests: {metrics['total_requests']}")
        st.write(f"Success Rate: {metrics['success_rate']:.2f}%")
        st.write(f"Avg Response Time: {metrics['avg_response_time']:.2f}s")
        if cache_enabled:
            st.write(f"Cache Hit Rate: {metrics['cache_hit_rate']:.2f}%")
    url = st.text_input("Enter Website URL")
    content_type = st.selectbox("Select Content Type", ['text', 'links', 'images', 'tables', 'webform', 'dynamic', 'article'])
    form_selector = st.text_input("Form Selector", value="form") if content_type == 'webform' else None
    if st.button("Start Scraping"):
        if url:
            try:
                with st.spinner("Scraping in progress..."):
                    result = asyncio.run(scraper.scrape_website(url, content_type, form_selector))
                st.subheader("Scraping Results")
                if content_type == 'text':
                    st.text_area("Extracted Text", result['data'], height=300)
                else:
                    st.json(result['data'])
                if result.get('metadata'):
                    with st.expander("Metadata"):
                        st.json(result['metadata'])
            except Exception as e:
                st.error(f"Scraping failed: {str(e)}")
        else:
            st.warning("Please enter a URL to scrape.")

if __name__ == "__main__":
    main()
